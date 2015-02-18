{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Record.Lens 
    ( mkRecordAliases
    , mkRecords
    , mkRecords'
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Foldable (foldMap)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import GHC.TypeLits
import Language.Haskell.TH

class Record (n :: Symbol) c s t a b | n s -> a, n t -> b, n a t -> s, n b s -> t, s n -> c where
    recordLens :: c f => proxy n -> (a -> f b) -> (s -> f t)

type Record' n c s a = Record n c s s a a

data RecordName (n :: Symbol) = RecordName

recordPresentClause :: Name -> Con -> Q Clause
recordPresentClause field (RecC conN recs) = do
    f <- newName "f"
    x <- newName "x"
    a <- newName "a"
    b <- newName "b"
    return $ Clause [WildP, VarP f, AsP x (RecP conN [(field, VarP a)])]
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
recordPresentClause _ _ = fail "Records aren't present in non-record fields"

recordAbsentClause :: Con -> Q Clause
recordAbsentClause (RecC conN recs) = do
    f <- newName "f"
    let rec_names = map (\(n, _, _) -> n) recs
    var_names <- traverse (\_ -> newName "a") recs
    return $ Clause [WildP, VarP f, RecP conN (zip rec_names (map VarP var_names))]
        (NormalB
            (AppE
                (VarE 'pure)
                (RecConE conN (zip rec_names (map VarE var_names)))
            )
        )
        []
recordAbsentClause (NormalC conN params) = do
    f <- newName "f"
    var_names <- traverse (\_ -> newName "p") params
    return $ Clause [WildP, VarP f, ConP conN (map VarP var_names)]
        (NormalB
            (AppE
                (VarE 'pure)
                (foldl AppE (ConE conN) (map VarE var_names))
            )
        )
        []
recordAbsentClause _ = fail "Unsuported constructor type"

recordPresent :: Name -> Con -> Bool
recordPresent recN (RecC conN recs) = any (\(n, _, _) -> n == recN) recs
recordPresent _ _ = False

recordLensClause :: Name -> Con -> Q Clause
recordLensClause recN con = if recordPresent recN con
    then recordPresentClause recN con
    else recordAbsentClause con

mkRecordInstance :: Name -> [TyVarBndr] -> String -> Name -> [Con] -> Q [Dec]
mkRecordInstance tyCon tyBndrs lensNameStr recN cons = do
    case findRecType recN cons of
        Nothing -> return []
        Just recTy -> do
            let lensName = mkName lensNameStr
            clauses <- traverse (recordLensClause recN) cons
            inTy <- instanceType tyCon tyBndrs lensNameStr recN cons
            return . return $ InstanceD []
                inTy
                [FunD 'recordLens clauses]
    where
    ty = appliedType tyCon tyBndrs

    fConstraint = if all (recordPresent recN) cons then ConT ''Functor else ConT ''Applicative

instanceType :: Name -> [TyVarBndr] -> String -> Name -> [Con] -> Q Type
instanceType tyCon tyBndrs lensNameStr recN cons = do
    let otherFieldTypes = do
            con <- cons
            case con of
                NormalC _ sts -> map snd sts
                RecC _ vsts -> do
                    (r_n, _, r_ty) <- vsts
                    if recN /= r_n
                        then [r_ty]
                        else []
                InfixC st1 _ st2 -> map snd [st1, st2]
                ForallC _ _ _ -> fail "forall types not supported"
        ty = appliedType tyCon tyBndrs
        Just recTy = findRecType recN cons
        constantTypeVars = foldMap containedTypeVars otherFieldTypes
        allFieldTypes = do
            con <- cons
            case con of
                NormalC _ sts -> map snd sts
                RecC _ vsts -> map (\(_, _, ty) -> ty) vsts
                InfixC st1 _ st2 -> map snd [st1, st2]
                ForallC _ _ _ -> fail "forall types not supported"
        allFieldTypeVars = foldMap containedTypeVars allFieldTypes
        allTypeVars = map bndrName tyBndrs
        phantomTypeVars = filter (not . flip Set.member allFieldTypeVars) allTypeVars
        typeVarMap = Map.fromList . map (\x -> (x, x)) $ Set.toList constantTypeVars ++ phantomTypeVars
        fConstraint = if all (recordPresent recN) cons then ConT ''Functor else ConT ''Applicative

    (ty', recTy') <- flip evalStateT typeVarMap $ (,) <$> buildReplacementType ty <*> buildReplacementType recTy
    return $ foldl AppT (ConT ''Record)
        [ (LitT (StrTyLit lensNameStr))
        , fConstraint
        , ty
        , ty'
        , recTy
        , recTy'
        ]
    where
    buildReplacementType :: Type -> StateT (Map Name Name) Q Type
    buildReplacementType (ForallT _ _ _) = lift (fail "forall types not supported")
    buildReplacementType (AppT ty1 ty2) = AppT <$> buildReplacementType ty1 <*> buildReplacementType ty2
    buildReplacementType (SigT ty k) = SigT <$> buildReplacementType ty <*> return k
    buildReplacementType (VarT n) = StateT $ \nameMap ->
        case Map.lookup n nameMap of
            Nothing -> do
                n' <- newName (nameBase n)
                return (VarT n', Map.insert n n' nameMap)
            Just n' -> return (VarT n', nameMap)
    buildReplacementType ty = return ty

containedTypeVars :: Type -> Set Name
containedTypeVars (ForallT _ _ _) = error "forall types not supported in records"
containedTypeVars (AppT t1 t2) = containedTypeVars t1 <> containedTypeVars t2
containedTypeVars (SigT t _) = containedTypeVars t
containedTypeVars (VarT n) = Set.singleton n
containedTypeVars _ = Set.empty

findRecType :: Name -> [Con] -> Maybe Type
findRecType _ [] = Nothing
findRecType recN ((RecC conN recs):rest) =
    case findRecType' recN recs of
        Just t -> Just t
        Nothing -> findRecType recN rest
findRecType recN (_:rest) = findRecType recN rest

findRecType' :: Name -> [(Name, Strict, Type)] -> Maybe Type
findRecType' _ [] = Nothing
findRecType' recN ((n, _, t):rest) = if n == recN
    then Just t
    else findRecType' recN rest

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

recordNames :: (String -> Maybe String) -> Con -> [(String, Name)]
recordNames nameRule (RecC _ recs) = recs >>= \(recN, _, _) ->
    case nameRule (nameBase recN) of
        Just lensNameStr -> [(lensNameStr, recN)]
        Nothing -> []
recordNames _ _ = []

mkRecordAliases :: (String -> Maybe String) -> [Con] -> Q [Dec]
mkRecordAliases nameRule = fmap concat . traverse recordLensAlias . fmap fst . (>>= recordNames nameRule)

mkRecords :: String -> Name -> Q [Dec]
mkRecords prefix tyN = do
    TyConI dec <- reify tyN
    case dec of
        DataD _ n vs cons _ -> do
            instances <- fmap concat . for (cons >>= recordNames nameRule) $ \(lensNameStr, recN) ->
                mkRecordInstance n vs lensNameStr recN cons
            aliases <- mkRecordAliases nameRule cons
            return $ instances ++ aliases
        NewtypeD _ n vs con _ -> do
            instances <- fmap concat . for (recordNames nameRule con) $ \(lensNameStr, recN) ->
                mkRecordInstance n vs lensNameStr recN [con]
            aliases <- mkRecordAliases nameRule [con]
            return $ instances ++ aliases
    where
    nameRule = prefixRule prefix

mkRecords' :: Name -> Q [Dec]
mkRecords' = mkRecords "_"
