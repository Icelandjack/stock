{-# LANGUAGE CPP #-}

-- | Cross-version shims for GHC API names that moved or were renamed.
--
-- GHC 9.10 split @base@ into @ghc-internal@, renaming the wired-in module
-- constants from @gHC_*@ to @gHC_INTERNAL_*@.  We expose the 9.10+ spelling
-- everywhere and map it back to the old names on 9.8.
module Stock.Compat
  ( gHC_INTERNAL_SHOW
  , gHC_INTERNAL_READ
  , gHC_INTERNAL_LIST
  , gHC_INTERNAL_GENERICS
  , tEXT_READPREC
  , tEXT_READ_LEX
  ) where

import GHC.Unit.Types (Module, mkModule, moduleUnit)
import GHC.Unit.Module (mkModuleName)

#if MIN_VERSION_ghc(9,10,0)
import GHC.Builtin.Names
  ( gHC_INTERNAL_SHOW, gHC_INTERNAL_READ
  , gHC_INTERNAL_LIST, gHC_INTERNAL_GENERICS )
#else
import GHC.Builtin.Names (gHC_SHOW, gHC_READ, gHC_LIST, gHC_GENERICS)

gHC_INTERNAL_SHOW, gHC_INTERNAL_READ, gHC_INTERNAL_LIST, gHC_INTERNAL_GENERICS :: Module
gHC_INTERNAL_SHOW     = gHC_SHOW
gHC_INTERNAL_READ     = gHC_READ
gHC_INTERNAL_LIST     = gHC_LIST
gHC_INTERNAL_GENERICS = gHC_GENERICS
#endif

-- @Text.ParserCombinators.ReadPrec@ and @Text.Read.Lex@ are not wired in; build
-- them in the same unit as @GHC.Read@ (base on <9.10, ghc-internal after), where
-- they moved under the @GHC.Internal.@ prefix alongside it.
tEXT_READPREC, tEXT_READ_LEX :: Module
#if MIN_VERSION_ghc(9,10,0)
tEXT_READPREC = mkModule (moduleUnit gHC_INTERNAL_READ) (mkModuleName "GHC.Internal.Text.ParserCombinators.ReadPrec")
tEXT_READ_LEX = mkModule (moduleUnit gHC_INTERNAL_READ) (mkModuleName "GHC.Internal.Text.Read.Lex")
#else
tEXT_READPREC = mkModule (moduleUnit gHC_INTERNAL_READ) (mkModuleName "Text.ParserCombinators.ReadPrec")
tEXT_READ_LEX = mkModule (moduleUnit gHC_INTERNAL_READ) (mkModuleName "Text.Read.Lex")
#endif
