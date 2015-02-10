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

data Pair a b = Pair { _first :: a, _second :: b }
    deriving (Eq, Show, Ord)

$(mkRecords ''Pair)
$(return $ recordLensAlias "first")
$(return $ recordLensAlias "second")
