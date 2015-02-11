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
import Data.List
import Data.Maybe
import Data.Traversable
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

-- TODO: Support type-changing updates.
-- Requires solving for a substitution dictionary as the record type can be a combination of the type variables
-- and other fields in the record type can prevent the ability to change types.
-- TODO: Generate traversals gracefully
-- TODO: Lenses for multiple constructors with the same record
mkRecordInstancesForCon :: (String -> Maybe String) -> Name -> [TyVarBndr] -> Con -> Q [Dec]
mkRecordInstancesForCon nameRule tyCon tyBndrs con = case con of
    RecC conN recs -> fmap catMaybes . for recs $ \(recN, _, recTy) ->
        case nameRule (nameBase recN) of
            Just lensNameStr -> do
                let lensName = mkName lensNameStr
                clause <- mkRecordLensClause conN recN
                t <- newName "t"
                b <- newName "b"
                let ty = appliedType tyCon tyBndrs
                return . Just $ InstanceD []
                    (foldl AppT (ConT ''Record)
                        [ (LitT (StrTyLit lensNameStr))
                        , (ConT ''Functor)
                        , ty
                        , ty
                        , recTy
                        , recTy
                        ]
                    )
                    [FunD 'recordLens [clause]]
            Nothing -> return Nothing
    _ -> return []

bndrName :: TyVarBndr -> Name
bndrName (PlainTV s) = s
bndrName (KindedTV s _) = s

appliedType :: Name -> [TyVarBndr] -> Type
appliedType con = foldl AppT (ConT con) . map (VarT . bndrName)

fullyAppliedTyCon :: Name -> [TyVarBndr] -> Q Type
fullyAppliedTyCon con = fmap (foldl AppT (ConT con)) . traverse (fmap VarT . newName . nameBase . bndrName)

recordLensAlias :: String -> Q [Dec]
recordLensAlias recN = do 
    mn <- lookupValueName recN
    case mn of
        Nothing -> return [signature, definition]
        Just _ -> return []
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

prefixRule :: String -> String -> Maybe String
prefixRule pre s = if pre `isPrefixOf` s
    then Just (drop (length pre) s)
    else Nothing

recordNames :: (String -> Maybe String) -> Con -> [(String, String)]
recordNames nameRule (RecC _ recs) = recs >>= \(recN, _, _) ->
    case nameRule (nameBase recN) of
        Just lensNameStr -> [(lensNameStr, nameBase recN)]
        Nothing -> []
recordNames _ _ = []

mkRecordAliases :: (String -> Maybe String) -> [Con] -> Q [Dec]
mkRecordAliases nameRule = fmap concat . traverse recordLensAlias . fmap fst . (>>= recordNames nameRule)

mkRecords :: String -> Name -> Q [Dec]
mkRecords prefix tyN = do
    TyConI dec <- reify tyN
    case dec of
        DataD _ n vs cons _ -> do
            instances <- fmap concat $ traverse (mkRecordInstancesForCon nameRule n vs) cons
            aliases <- mkRecordAliases nameRule cons
            return $ instances ++ aliases
        NewtypeD _ n vs con _ -> do
            instances <- mkRecordInstancesForCon nameRule n vs con
            aliases <- mkRecordAliases nameRule [con]
            return $ instances ++ aliases
    where
    nameRule = prefixRule prefix

mkRecords' :: Name -> Q [Dec]
mkRecords' = mkRecords "_"
