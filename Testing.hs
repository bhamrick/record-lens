{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

-- These are required for my hack around ambiguous variables
-- Would prefer to remove these requirements.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Language.Record.Lens

data Pair a b = Pair { p_first :: a, p_second :: b }
    deriving (Eq, Show, Ord)

data IntPair = IntPair { ip_first :: Int, ip_second :: Int }
    deriving (Eq, Show, Ord)

$(mkRecords "p_" ''Pair)
$(mkRecords "ip_" ''IntPair)
