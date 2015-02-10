{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Record.Lens where

import Control.Monad
import Data.Maybe
import GHC.TypeLits
import Language.Haskell.TH

class Record (n :: Symbol) c s t a b | n s -> a, n t -> b, n a t -> s, n b s -> t, s n -> c where
    recordLens :: c f => proxy n -> (a -> f b) -> (s -> f t)

type Record' n c s a = Record n c s s a a

data RecordName (n :: Symbol) = RecordName

instance Record "1" Functor (a, x) (b, x) a b where
    recordLens _ f (a, x) = fmap (flip (,) x) (f a)

_1 :: (Record "1" c s t a b, c f) => (a -> f b) -> (s -> f t)
_1 = recordLens (RecordName :: RecordName "1")

data Stupid = Stupid { _stupid :: Int }
    deriving (Eq, Show, Ord)

stupid :: Functor f => (Int -> f Int) -> Stupid -> f Stupid
stupid f x = fmap (\b -> x { _stupid = b}) (f (_stupid x))

mkRecordLensClause :: Name -> Name -> Q Clause
mkRecordLensClause con field = do
    f <- newName "f"
    x <- newName "x"
    a <- newName "a"
    b <- newName "b"
    return $ Clause [WildP, VarP f, AsP x (RecP con [(field, VarP a)])]
        (NormalB (AppE
            (AppE
                (VarE 'fmap)
                (LamE [VarP b]
                    (RecUpdE (VarE x) [(field, VarE b)])
                )
            )
            (AppE
                (VarE f)
                (VarE a)
            )
        ))
        []

mkRecordInstancesForCon :: Type -> Con -> Q [Dec]
mkRecordInstancesForCon ty con = case con of
    RecC conN recs -> fmap catMaybes . forM recs $ \(recN, _, recTy) ->
        case nameBase recN of
            '_':lensNameStr -> do
                let lensName = mkName lensNameStr
                clause <- mkRecordLensClause conN recN
                t <- newName "t"
                b <- newName "b"
                return . Just $ InstanceD [EqualP ty (VarT t), EqualP recTy (VarT b)]
                    (foldl AppT (ConT ''Record)
                        [ (LitT (StrTyLit lensNameStr))
                        , (ConT ''Functor)
                        , ty
                        , (VarT t)
                        , recTy
                        , (VarT b)
                        ]
                    )
                    [FunD 'recordLens [clause]]
            _ -> return Nothing
    _ -> return []

bndrName :: TyVarBndr -> Name
bndrName (PlainTV s) = s
bndrName (KindedTV s _) = s

appliedType :: Name -> [TyVarBndr] -> Type
appliedType con = foldl AppT (ConT con) . map (VarT . bndrName)

recordLensAlias :: String -> [Dec]
recordLensAlias recN = [signature, definition]
    where
    lensName = mkName recN
    signature = 
        let c = mkName "c"
            s = mkName "s"
            t = mkName "t"
            a = mkName "a"
            b = mkName "b"
            f = mkName "f"
        in
        SigD lensName (ForallT
            (map PlainTV [c, s, t, a, b, f])
            [ClassP ''Record [LitT (StrTyLit recN), VarT c, VarT s, VarT t, VarT a, VarT b], ClassP c [VarT f]]
            (functionT
                (functionT
                    (VarT a)
                    (AppT (VarT f) (VarT b))
                )
                (functionT
                    (VarT s)
                    (AppT (VarT f) (VarT t))
                )
            )
        )
    functionT t1 t2 = AppT (AppT ArrowT t1) t2
    definition = FunD lensName [Clause [] (NormalB aliasExp) []]
    aliasExp = AppE (VarE 'recordLens) (SigE (ConE 'RecordName) (AppT (ConT ''RecordName) (LitT (StrTyLit recN))))

mkRecords :: Name -> Q [Dec]
mkRecords tyN = do
    TyConI dec <- reify tyN
    case dec of
        DataD _ n vs cons _ -> 
            fmap concat $ mapM (mkRecordInstancesForCon (appliedType n vs)) cons
        NewtypeD _ n vs con _ -> 
            mkRecordInstancesForCon (appliedType n vs) con
