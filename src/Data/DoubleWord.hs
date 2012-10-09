{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module provides strict (low and high halves are unpacked)
--   signed and unsigned binary word data types of sizes 96, 128,
--   160, 192, 224, and 256 bits.
module Data.DoubleWord
  ( module Data.DoubleWord.Base
  , Word96(..)
  , Word128(..)
  , Word160(..)
  , Word192(..)
  , Word224(..)
  , Word256(..)
  , Int96(..)
  , Int128(..)
  , Int160(..)
  , Int192(..)
  , Int224(..)
  , Int256(..)
  ) where

import Data.Word
import Data.Int
import Data.DoubleWord.Base
import Data.DoubleWord.TH

mkUnpackedDoubleWord "Word96"  ''Word32  "Int96"  ''Int32  ''Word64
mkUnpackedDoubleWord "Word128" ''Word64  "Int128" ''Int64  ''Word64
mkUnpackedDoubleWord "Word160" ''Word32  "Int160" ''Int32  ''Word128
mkUnpackedDoubleWord "Word192" ''Word64  "Int192" ''Int64  ''Word128
mkUnpackedDoubleWord "Word224" ''Word96  "Int224" ''Int96  ''Word128
mkUnpackedDoubleWord "Word256" ''Word128 "Int256" ''Int128 ''Word128

