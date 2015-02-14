{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

import Language.Record.Lens

data Pair a b = Pair { p_first :: a, p_second :: b }
    deriving (Eq, Show, Ord)

data IntPair = IntPair { ip_first :: Int, ip_second :: Int }
    deriving (Eq, Show, Ord)

$(mkRecords "p_" ''Pair)
$(mkRecords "ip_" ''IntPair)

data RecMaybe a = RecNothing | RecJust { rm_just :: a }
    deriving (Eq, Show, Ord)

$(mkRecords "rm_" ''RecMaybe)

data OneOf a b = L { _l :: a } | R { _r :: b }
    deriving (Eq, Show, Ord)

$(mkRecords "_" ''OneOf)

-- Works fine with function types
data OldLens s t a b = OldLens { _getter :: s -> a, _setter :: s -> b -> t }

$(mkRecords "_" ''OldLens)

-- Record lenses cannot change phantom types in order to preserve the functional dependencies
newtype Phantom a b = Phantom { _phant :: b }
    deriving (Eq, Show, Ord)

$(mkRecords "_" ''Phantom)
