{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

-- | This module provides strict (low and high halves are unpacked)
--   signed and unsigned binary word data types of sizes 96, 128,
--   160, 192, 224, and 256 bits.
module Data.DoubleWord
  ( module Data.BinaryWord
  , module Data.DoubleWord.Base
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

import Data.Data
import GHC.Generics
import Data.Word
import Data.Int
import Data.BinaryWord
import Data.DoubleWord.Base
import Data.Hashable
import GHC.Arr
import Data.Bits
import Data.Ratio

data Word96
  = Word96 {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word64
  deriving (Typeable, Data, Generic)
instance DoubleWord Word96 where
  type LoWord Word96 = Word64
  type HiWord Word96 = Word32
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word96 _ lo_) = lo_
  hiWord (Word96 hi_ _) = hi_
  fromHiAndLo = Word96
  extendLo x = (Word96 allZeroes) x
  signExtendLo x
    = (Word96 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word96 where
  {-# INLINE (==) #-}
  (==) (Word96 hi_ lo_) (Word96 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word96 where
  {-# INLINABLE compare #-}
  compare (Word96 hi_ lo_) (Word96 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word96 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word96 minBound) minBound
  maxBound = (Word96 maxBound) maxBound
instance Enum Word96 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word96 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word96 (succ hi_)) minBound
      else
          (Word96 hi_) (succ lo_)
  pred (Word96 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word96 (pred hi_)) maxBound
      else
          (Word96 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word96 allZeroes) (toEnum x)
  fromEnum (Word96 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word96 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word96 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word96 (negate hi_)) allZeroes
      else
          (Word96 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word96 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word96 hi_ lo_) (Word96 hi' lo')
    = (Word96 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word96 hi_ lo_) (Word96 hi' lo')
    = (Word96
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word96 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word64))) 1)
instance Real Word96 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word96 where
  {-# INLINE divMod #-}
  toInteger (Word96 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_)) (((+) (toInteger (maxBound :: Word64))) 1)))
        (toInteger lo_)
  quotRem x@(Word96 hi_ lo_) y@(Word96 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word96 allZeroes) t2, (Word96 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word96 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word96 allZeroes) (fromIntegral t2),
                  (Word96 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word96 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word96 allZeroes) z, (Word96 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word96 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word96 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word96 allZeroes) z)) lsb,
                              (Word96 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word96 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word96 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word32))) t2)
                  Word96 hhh hll = (shiftL x) t2
                  v@(Word96 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word96 (fromIntegral t4)) t3
                  t6 = (Word96 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word96 (fromIntegral t8)) t7)) ((Word96 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word96 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word96 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word96 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word96 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word96 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word96 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word96 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word32)))
        (finiteBitSize (undefined :: Word64))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word96 hi_ lo_)
    = (Word96 (complement hi_)) (complement lo_)
  xor (Word96 hi_ lo_) (Word96 hi' lo')
    = (Word96 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word96 hi_ lo_) (Word96 hi' lo')
    = (Word96 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word96 hi_ lo_) (Word96 hi' lo')
    = (Word96 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word96 hi_ lo_) x
    = if ((>) y) 0 then
          (Word96 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word96 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
  shiftR (Word96 hi_ lo_) x
    = (Word96 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word96 (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word64))) z)))
               ((shiftR lo_) z))
      else
          (Word96
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word64))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
        z = ((-) (finiteBitSize (undefined :: Word96))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word96))) y)
  bit x
    = if ((>=) y) 0 then
          (Word96 (bit y)) allZeroes
      else
          (Word96 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  setBit (Word96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word96 ((setBit hi_) y)) lo_
      else
          (Word96 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word64))
  clearBit (Word96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word96 ((clearBit hi_) y)) lo_
      else
          (Word96 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  complementBit (Word96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word96 ((complementBit hi_) y)) lo_
      else
          (Word96 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  testBit (Word96 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  popCount (Word96 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word96 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word32)))
        (finiteBitSize (undefined :: Word64))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word96 where
  type UnsignedWord Word96 = Word96
  type SignedWord Word96 = Int96
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word96 hi_ lo_) = (Int96 (signedWord hi_)) lo_
  unwrappedAdd (Word96 hi_ lo_) (Word96 hi' lo')
    = ((Word96 allZeroes) z, (Word96 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word96 hi_ lo_) (Word96 hi' lo')
    = ((Word96
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word96 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word32)
        z = ((-) (finiteBitSize (undefined :: Word64))) y
  leadingZeroes (Word96 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word32)
  trailingZeroes (Word96 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word64)
  allZeroes = (Word96 allZeroes) allZeroes
  allOnes = (Word96 allOnes) allOnes
  msb = (Word96 msb) allZeroes
  lsb = (Word96 allZeroes) lsb
  testMsb (Word96 hi_ _) = testMsb hi_
  testLsb (Word96 _ lo_) = testLsb lo_
  setMsb (Word96 hi_ lo_) = (Word96 (setMsb hi_)) lo_
  setLsb (Word96 hi_ lo_) = (Word96 hi_) (setLsb lo_)
  clearMsb (Word96 hi_ lo_) = (Word96 (clearMsb hi_)) lo_
  clearLsb (Word96 hi_ lo_) = (Word96 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word96->GHC.Word.Word64"
              fromIntegral
                = loWord :: Word96 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word96"
              fromIntegral
                = extendLo :: Word64 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) loWord :: Word96 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word96"
              fromIntegral
                = signExtendLo :: Int64 -> Word96 #-}
{-# RULES "fromIntegral/Word96->Word96"
              fromIntegral
                = id :: Word96 -> Word96 #-}
{-# RULES "fromIntegral/Word96->Int96"
              fromIntegral
                = signedWord :: Word96 -> Int96 #-}
{-# RULES "fromIntegral/Word96->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word32 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int32 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word16 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int16 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word8 -> Word96 #-}
{-# RULES "fromIntegral/Word96->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word96 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int8 -> Word96 #-}
data Int96
  = Int96 {-# UNPACK #-} !Int32 {-# UNPACK #-} !Word64
  deriving (Typeable, Data, Generic)
instance DoubleWord Int96 where
  type LoWord Int96 = Word64
  type HiWord Int96 = Int32
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int96 _ lo_) = lo_
  hiWord (Int96 hi_ _) = hi_
  fromHiAndLo = Int96
  extendLo x = (Int96 allZeroes) x
  signExtendLo x
    = (Int96 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int96 where
  {-# INLINE (==) #-}
  (==) (Int96 hi_ lo_) (Int96 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int96 where
  {-# INLINABLE compare #-}
  compare (Int96 hi_ lo_) (Int96 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int96 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int96 minBound) minBound
  maxBound = (Int96 maxBound) maxBound
instance Enum Int96 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int96 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int96 (succ hi_)) minBound
      else
          (Int96 hi_) (succ lo_)
  pred (Int96 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int96 (pred hi_)) maxBound
      else
          (Int96 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int96 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int96 allZeroes) (toEnum x)
  fromEnum (Int96 0 lo_) = fromEnum lo_
  fromEnum (Int96 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int96 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int96 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int96 (negate hi_)) allZeroes
      else
          (Int96 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int96 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int96 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int96 hi_ lo_) (Int96 hi' lo')
    = (Int96 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int96 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word64))) 1)
instance Real Int96 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int96 where
  toInteger (Int96 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_)) (((+) (toInteger (maxBound :: Word64))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int96 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int96 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int96 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int96 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int96 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int96 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int32)))
        (finiteBitSize (undefined :: Word64))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int96 hi_ lo_)
    = (Int96 (complement hi_)) (complement lo_)
  xor (Int96 hi_ lo_) (Int96 hi' lo')
    = (Int96 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int96 hi_ lo_) (Int96 hi' lo')
    = (Int96 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int96 hi_ lo_) (Int96 hi' lo')
    = (Int96 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int96 hi_ lo_) x
    = if ((>) y) 0 then
          (Int96 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int96 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
  shiftR (Int96 hi_ lo_) x
    = (Int96 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word64)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int96))) y)
  bit x
    = if ((>=) y) 0 then
          (Int96 (bit y)) allZeroes
      else
          (Int96 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  setBit (Int96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int96 ((setBit hi_) y)) lo_
      else
          (Int96 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word64))
  clearBit (Int96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int96 ((clearBit hi_) y)) lo_
      else
          (Int96 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  complementBit (Int96 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int96 ((complementBit hi_) y)) lo_
      else
          (Int96 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  testBit (Int96 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  popCount (Int96 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int96 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int32)))
        (finiteBitSize (undefined :: Word64))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int96 where
  type UnsignedWord Int96 = Word96
  type SignedWord Int96 = Int96
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int96 hi_ lo_) = (Word96 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int96 hi_ lo_) (Int96 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int96 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int96 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word96 (unsignedWord hi_)) lo_))
              ((Word96 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int96 allZeroes) allZeroes
  allOnes = (Int96 allOnes) allOnes
  msb = (Int96 msb) allZeroes
  lsb = (Int96 allZeroes) lsb
  testMsb (Int96 hi_ _) = testMsb hi_
  testLsb (Int96 _ lo_) = testLsb lo_
  setMsb (Int96 hi_ lo_) = (Int96 (setMsb hi_)) lo_
  setLsb (Int96 hi_ lo_) = (Int96 hi_) (setLsb lo_)
  clearMsb (Int96 hi_ lo_) = (Int96 (clearMsb hi_)) lo_
  clearLsb (Int96 hi_ lo_) = (Int96 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int96->GHC.Word.Word64"
              fromIntegral
                = loWord :: Int96 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int96"
              fromIntegral
                = extendLo :: Word64 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) loWord :: Int96 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int96"
              fromIntegral
                = signExtendLo :: Int64 -> Int96 #-}
{-# RULES "fromIntegral/Int96->Int96"
              fromIntegral
                = id :: Int96 -> Int96 #-}
{-# RULES "fromIntegral/Int96->Word96"
              fromIntegral
                = unsignedWord :: Int96 -> Word96 #-}
{-# RULES "fromIntegral/Int96->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word32 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int32 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word16 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int16 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int96"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word8 -> Int96 #-}
{-# RULES "fromIntegral/Int96->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int96 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int96"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int8 -> Int96 #-}
  
data Word128
  = Word128 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
  deriving (Typeable, Data, Generic)
instance DoubleWord Word128 where
  type LoWord Word128 = Word64
  type HiWord Word128 = Word64
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word128 _ lo_) = lo_
  hiWord (Word128 hi_ _) = hi_
  fromHiAndLo = Word128
  extendLo x = (Word128 allZeroes) x
  signExtendLo x
    = (Word128 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word128 where
  {-# INLINE (==) #-}
  (==) (Word128 hi_ lo_) (Word128 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word128 where
  {-# INLINABLE compare #-}
  compare (Word128 hi_ lo_) (Word128 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word128 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word128 minBound) minBound
  maxBound = (Word128 maxBound) maxBound
instance Enum Word128 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word128 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word128 (succ hi_)) minBound
      else
          (Word128 hi_) (succ lo_)
  pred (Word128 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word128 (pred hi_)) maxBound
      else
          (Word128 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word128 allZeroes) (toEnum x)
  fromEnum (Word128 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word128 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word128 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word128 (negate hi_)) allZeroes
      else
          (Word128 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word128 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word128 hi_ lo_) (Word128 hi' lo')
    = (Word128 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word128 hi_ lo_) (Word128 hi' lo')
    = (Word128
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word128 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word64))) 1)
instance Real Word128 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word128 where
  {-# INLINE divMod #-}
  toInteger (Word128 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_)) (((+) (toInteger (maxBound :: Word64))) 1)))
        (toInteger lo_)
  quotRem x@(Word128 hi_ lo_) y@(Word128 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word128 allZeroes) t2, (Word128 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word128 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word128 allZeroes) (fromIntegral t2),
                  (Word128 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word128 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word128 allZeroes) z, (Word128 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word128 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word128 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word128 allZeroes) z)) lsb,
                              (Word128 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word128 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word128 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word64))) t2)
                  Word128 hhh hll = (shiftL x) t2
                  v@(Word128 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word128 (fromIntegral t4)) t3
                  t6 = (Word128 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word128 (fromIntegral t8)) t7))
                            ((Word128 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word128 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word128 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word128 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word128 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word128 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word128 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word128 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word64)))
        (finiteBitSize (undefined :: Word64))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word128 hi_ lo_)
    = (Word128 (complement hi_)) (complement lo_)
  xor (Word128 hi_ lo_) (Word128 hi' lo')
    = (Word128 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word128 hi_ lo_) (Word128 hi' lo')
    = (Word128 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word128 hi_ lo_) (Word128 hi' lo')
    = (Word128 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word128 hi_ lo_) x
    = if ((>) y) 0 then
          (Word128
             (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word128 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
  shiftR (Word128 hi_ lo_) x
    = (Word128 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word128
             (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word64))) z)))
               ((shiftR lo_) z))
      else
          (Word128
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word64))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
        z = ((-) (finiteBitSize (undefined :: Word128))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word128))) y)
  bit x
    = if ((>=) y) 0 then
          (Word128 (bit y)) allZeroes
      else
          (Word128 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  setBit (Word128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word128 ((setBit hi_) y)) lo_
      else
          (Word128 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word64))
  clearBit (Word128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word128 ((clearBit hi_) y)) lo_
      else
          (Word128 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  complementBit (Word128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word128 ((complementBit hi_) y)) lo_
      else
          (Word128 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  testBit (Word128 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  popCount (Word128 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word128 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word64)))
        (finiteBitSize (undefined :: Word64))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word128 where
  type UnsignedWord Word128 = Word128
  type SignedWord Word128 = Int128
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word128 hi_ lo_) = (Int128 (signedWord hi_)) lo_
  unwrappedAdd (Word128 hi_ lo_) (Word128 hi' lo')
    = ((Word128 allZeroes) z, (Word128 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word128 hi_ lo_) (Word128 hi' lo')
    = ((Word128
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word128 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word64)
        z = ((-) (finiteBitSize (undefined :: Word64))) y
  leadingZeroes (Word128 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word64)
  trailingZeroes (Word128 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word64)
  allZeroes = (Word128 allZeroes) allZeroes
  allOnes = (Word128 allOnes) allOnes
  msb = (Word128 msb) allZeroes
  lsb = (Word128 allZeroes) lsb
  testMsb (Word128 hi_ _) = testMsb hi_
  testLsb (Word128 _ lo_) = testLsb lo_
  setMsb (Word128 hi_ lo_) = (Word128 (setMsb hi_)) lo_
  setLsb (Word128 hi_ lo_) = (Word128 hi_) (setLsb lo_)
  clearMsb (Word128 hi_ lo_) = (Word128 (clearMsb hi_)) lo_
  clearLsb (Word128 hi_ lo_) = (Word128 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word128->GHC.Word.Word64"
              fromIntegral
                = loWord :: Word128 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word128"
              fromIntegral
                = extendLo :: Word64 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) loWord :: Word128 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word128"
              fromIntegral
                = signExtendLo :: Int64 -> Word128 #-}
{-# RULES "fromIntegral/Word128->Word128"
              fromIntegral
                = id :: Word128 -> Word128 #-}
{-# RULES "fromIntegral/Word128->Int128"
              fromIntegral
                = signedWord :: Word128 -> Int128 #-}
{-# RULES "fromIntegral/Word128->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word32 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int32 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word16 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int16 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word8 -> Word128 #-}
{-# RULES "fromIntegral/Word128->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Word128 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int8 -> Word128 #-}
data Int128
  = Int128 {-# UNPACK #-} !Int64 {-# UNPACK #-} !Word64
  deriving (Typeable, Data, Generic)
instance DoubleWord Int128 where
  type LoWord Int128 = Word64
  type HiWord Int128 = Int64
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int128 _ lo_) = lo_
  hiWord (Int128 hi_ _) = hi_
  fromHiAndLo = Int128
  extendLo x = (Int128 allZeroes) x
  signExtendLo x
    = (Int128 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int128 where
  {-# INLINE (==) #-}
  (==) (Int128 hi_ lo_) (Int128 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int128 where
  {-# INLINABLE compare #-}
  compare (Int128 hi_ lo_) (Int128 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int128 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int128 minBound) minBound
  maxBound = (Int128 maxBound) maxBound
instance Enum Int128 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int128 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int128 (succ hi_)) minBound
      else
          (Int128 hi_) (succ lo_)
  pred (Int128 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int128 (pred hi_)) maxBound
      else
          (Int128 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int128 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int128 allZeroes) (toEnum x)
  fromEnum (Int128 0 lo_) = fromEnum lo_
  fromEnum (Int128 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int128 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int128 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int128 (negate hi_)) allZeroes
      else
          (Int128 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int128 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int128 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int128 hi_ lo_) (Int128 hi' lo')
    = (Int128 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int128 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word64))) 1)
instance Real Int128 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int128 where
  toInteger (Int128 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_)) (((+) (toInteger (maxBound :: Word64))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int128 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int128 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int128 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int128 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int128 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int128 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int64)))
        (finiteBitSize (undefined :: Word64))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int128 hi_ lo_)
    = (Int128 (complement hi_)) (complement lo_)
  xor (Int128 hi_ lo_) (Int128 hi' lo')
    = (Int128 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int128 hi_ lo_) (Int128 hi' lo')
    = (Int128 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int128 hi_ lo_) (Int128 hi' lo')
    = (Int128 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int128 hi_ lo_) x
    = if ((>) y) 0 then
          (Int128 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int128 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
  shiftR (Int128 hi_ lo_) x
    = (Int128 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word64))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word64)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int128))) y)
  bit x
    = if ((>=) y) 0 then
          (Int128 (bit y)) allZeroes
      else
          (Int128 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  setBit (Int128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int128 ((setBit hi_) y)) lo_
      else
          (Int128 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word64))
  clearBit (Int128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int128 ((clearBit hi_) y)) lo_
      else
          (Int128 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  complementBit (Int128 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int128 ((complementBit hi_) y)) lo_
      else
          (Int128 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  testBit (Int128 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word64))
  popCount (Int128 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int128 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int64)))
        (finiteBitSize (undefined :: Word64))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int128 where
  type UnsignedWord Int128 = Word128
  type SignedWord Int128 = Int128
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int128 hi_ lo_) = (Word128 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int128 hi_ lo_) (Int128 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int128 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int128 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word128 (unsignedWord hi_)) lo_))
              ((Word128 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int128 allZeroes) allZeroes
  allOnes = (Int128 allOnes) allOnes
  msb = (Int128 msb) allZeroes
  lsb = (Int128 allZeroes) lsb
  testMsb (Int128 hi_ _) = testMsb hi_
  testLsb (Int128 _ lo_) = testLsb lo_
  setMsb (Int128 hi_ lo_) = (Int128 (setMsb hi_)) lo_
  setLsb (Int128 hi_ lo_) = (Int128 hi_) (setLsb lo_)
  clearMsb (Int128 hi_ lo_) = (Int128 (clearMsb hi_)) lo_
  clearLsb (Int128 hi_ lo_) = (Int128 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int128->GHC.Word.Word64"
              fromIntegral
                = loWord :: Int128 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int128"
              fromIntegral
                = extendLo :: Word64 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) loWord :: Int128 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int128"
              fromIntegral
                = signExtendLo :: Int64 -> Int128 #-}
{-# RULES "fromIntegral/Int128->Int128"
              fromIntegral
                = id :: Int128 -> Int128 #-}
{-# RULES "fromIntegral/Int128->Word128"
              fromIntegral
                = unsignedWord :: Int128 -> Word128 #-}
{-# RULES "fromIntegral/Int128->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word32 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int32 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word16 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int16 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int128"
              fromIntegral
                = ((.) extendLo) fromIntegral :: Word8 -> Int128 #-}
{-# RULES "fromIntegral/Int128->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) loWord :: Int128 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int128"
              fromIntegral
                = ((.) signExtendLo) fromIntegral :: Int8 -> Int128 #-}

data Word160
  = Word160 {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Word160 where
  type LoWord Word160 = Word128
  type HiWord Word160 = Word32
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word160 _ lo_) = lo_
  hiWord (Word160 hi_ _) = hi_
  fromHiAndLo = Word160
  extendLo x = (Word160 allZeroes) x
  signExtendLo x
    = (Word160 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word160 where
  {-# INLINE (==) #-}
  (==) (Word160 hi_ lo_) (Word160 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word160 where
  {-# INLINABLE compare #-}
  compare (Word160 hi_ lo_) (Word160 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word160 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word160 minBound) minBound
  maxBound = (Word160 maxBound) maxBound
instance Enum Word160 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word160 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word160 (succ hi_)) minBound
      else
          (Word160 hi_) (succ lo_)
  pred (Word160 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word160 (pred hi_)) maxBound
      else
          (Word160 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word160 allZeroes) (toEnum x)
  fromEnum (Word160 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word160 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word160 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word160 (negate hi_)) allZeroes
      else
          (Word160 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word160 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word160 hi_ lo_) (Word160 hi' lo')
    = (Word160 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word160 hi_ lo_) (Word160 hi' lo')
    = (Word160
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word160 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Word160 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word160 where
  {-# INLINE divMod #-}
  toInteger (Word160 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x@(Word160 hi_ lo_) y@(Word160 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word160 allZeroes) t2, (Word160 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word160 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word160 allZeroes) (fromIntegral t2),
                  (Word160 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word160 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word160 allZeroes) z, (Word160 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word160 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word160 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word160 allZeroes) z)) lsb,
                              (Word160 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word160 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word160 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word32))) t2)
                  Word160 hhh hll = (shiftL x) t2
                  v@(Word160 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word160 (fromIntegral t4)) t3
                  t6 = (Word160 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word160 (fromIntegral t8)) t7))
                            ((Word160 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word160 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word160 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word160 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word160 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word160 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word160 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word160 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word32)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word160 hi_ lo_)
    = (Word160 (complement hi_)) (complement lo_)
  xor (Word160 hi_ lo_) (Word160 hi' lo')
    = (Word160 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word160 hi_ lo_) (Word160 hi' lo')
    = (Word160 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word160 hi_ lo_) (Word160 hi' lo')
    = (Word160 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word160 hi_ lo_) x
    = if ((>) y) 0 then
          (Word160
             (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word160 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Word160 hi_ lo_) x
    = (Word160 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word160
             (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               ((shiftR lo_) z))
      else
          (Word160
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
        z = ((-) (finiteBitSize (undefined :: Word160))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word160))) y)
  bit x
    = if ((>=) y) 0 then
          (Word160 (bit y)) allZeroes
      else
          (Word160 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Word160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word160 ((setBit hi_) y)) lo_
      else
          (Word160 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Word160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word160 ((clearBit hi_) y)) lo_
      else
          (Word160 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Word160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word160 ((complementBit hi_) y)) lo_
      else
          (Word160 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Word160 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Word160 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word160 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word32)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word160 where
  type UnsignedWord Word160 = Word160
  type SignedWord Word160 = Int160
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word160 hi_ lo_) = (Int160 (signedWord hi_)) lo_
  unwrappedAdd (Word160 hi_ lo_) (Word160 hi' lo')
    = ((Word160 allZeroes) z, (Word160 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word160 hi_ lo_) (Word160 hi' lo')
    = ((Word160
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word160 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word32)
        z = ((-) (finiteBitSize (undefined :: Word128))) y
  leadingZeroes (Word160 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word32)
  trailingZeroes (Word160 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word128)
  allZeroes = (Word160 allZeroes) allZeroes
  allOnes = (Word160 allOnes) allOnes
  msb = (Word160 msb) allZeroes
  lsb = (Word160 allZeroes) lsb
  testMsb (Word160 hi_ _) = testMsb hi_
  testLsb (Word160 _ lo_) = testLsb lo_
  setMsb (Word160 hi_ lo_) = (Word160 (setMsb hi_)) lo_
  setLsb (Word160 hi_ lo_) = (Word160 hi_) (setLsb lo_)
  clearMsb (Word160 hi_ lo_) = (Word160 (clearMsb hi_)) lo_
  clearLsb (Word160 hi_ lo_) = (Word160 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word160->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Word160 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word160"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Word160 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word160"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Word160 #-}
{-# RULES "fromIntegral/Word160->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Word160 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Word160"
              fromIntegral
                = extendLo :: Word128 -> Word160 #-}
{-# RULES "fromIntegral/Word160->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Word160 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Word160"
              fromIntegral
                = signExtendLo :: Int128 -> Word160 #-}
{-# RULES "fromIntegral/Word160->Word160"
              fromIntegral
                = id :: Word160 -> Word160 #-}
{-# RULES "fromIntegral/Word160->Int160"
              fromIntegral
                = signedWord :: Word160 -> Int160 #-}
{-# RULES "fromIntegral/Word160->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Word160 #-}
{-# RULES "fromIntegral/Word160->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word160 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Word160 #-}
data Int160
  = Int160 {-# UNPACK #-} !Int32 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Int160 where
  type LoWord Int160 = Word128
  type HiWord Int160 = Int32
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int160 _ lo_) = lo_
  hiWord (Int160 hi_ _) = hi_
  fromHiAndLo = Int160
  extendLo x = (Int160 allZeroes) x
  signExtendLo x
    = (Int160 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int160 where
  {-# INLINE (==) #-}
  (==) (Int160 hi_ lo_) (Int160 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int160 where
  {-# INLINABLE compare #-}
  compare (Int160 hi_ lo_) (Int160 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int160 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int160 minBound) minBound
  maxBound = (Int160 maxBound) maxBound
instance Enum Int160 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int160 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int160 (succ hi_)) minBound
      else
          (Int160 hi_) (succ lo_)
  pred (Int160 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int160 (pred hi_)) maxBound
      else
          (Int160 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int160 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int160 allZeroes) (toEnum x)
  fromEnum (Int160 0 lo_) = fromEnum lo_
  fromEnum (Int160 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int160 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int160 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int160 (negate hi_)) allZeroes
      else
          (Int160 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int160 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int160 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int160 hi_ lo_) (Int160 hi' lo')
    = (Int160 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int160 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Int160 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int160 where
  toInteger (Int160 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int160 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int160 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int160 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int160 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int160 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int160 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int32)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int160 hi_ lo_)
    = (Int160 (complement hi_)) (complement lo_)
  xor (Int160 hi_ lo_) (Int160 hi' lo')
    = (Int160 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int160 hi_ lo_) (Int160 hi' lo')
    = (Int160 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int160 hi_ lo_) (Int160 hi' lo')
    = (Int160 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int160 hi_ lo_) x
    = if ((>) y) 0 then
          (Int160 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int160 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Int160 hi_ lo_) x
    = (Int160 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word128)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int160))) y)
  bit x
    = if ((>=) y) 0 then
          (Int160 (bit y)) allZeroes
      else
          (Int160 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Int160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int160 ((setBit hi_) y)) lo_
      else
          (Int160 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Int160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int160 ((clearBit hi_) y)) lo_
      else
          (Int160 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Int160 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int160 ((complementBit hi_) y)) lo_
      else
          (Int160 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Int160 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Int160 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int160 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int32)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int160 where
  type UnsignedWord Int160 = Word160
  type SignedWord Int160 = Int160
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int160 hi_ lo_) = (Word160 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int160 hi_ lo_) (Int160 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int160 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int160 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word160 (unsignedWord hi_)) lo_))
              ((Word160 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int160 allZeroes) allZeroes
  allOnes = (Int160 allOnes) allOnes
  msb = (Int160 msb) allZeroes
  lsb = (Int160 allZeroes) lsb
  testMsb (Int160 hi_ _) = testMsb hi_
  testLsb (Int160 _ lo_) = testLsb lo_
  setMsb (Int160 hi_ lo_) = (Int160 (setMsb hi_)) lo_
  setLsb (Int160 hi_ lo_) = (Int160 hi_) (setLsb lo_)
  clearMsb (Int160 hi_ lo_) = (Int160 (clearMsb hi_)) lo_
  clearLsb (Int160 hi_ lo_) = (Int160 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int160->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Int160 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int160"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Int160 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int160"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Int160 #-}
{-# RULES "fromIntegral/Int160->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Int160 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Int160"
              fromIntegral
                = extendLo :: Word128 -> Int160 #-}
{-# RULES "fromIntegral/Int160->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Int160 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Int160"
              fromIntegral
                = signExtendLo :: Int128 -> Int160 #-}
{-# RULES "fromIntegral/Int160->Int160"
              fromIntegral
                = id :: Int160 -> Int160 #-}
{-# RULES "fromIntegral/Int160->Word160"
              fromIntegral
                = unsignedWord :: Int160 -> Word160 #-}
{-# RULES "fromIntegral/Int160->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int160"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Int160 #-}
{-# RULES "fromIntegral/Int160->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int160 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int160"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Int160 #-}

data Word192
  = Word192 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Word192 where
  type LoWord Word192 = Word128
  type HiWord Word192 = Word64
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word192 _ lo_) = lo_
  hiWord (Word192 hi_ _) = hi_
  fromHiAndLo = Word192
  extendLo x = (Word192 allZeroes) x
  signExtendLo x
    = (Word192 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word192 where
  {-# INLINE (==) #-}
  (==) (Word192 hi_ lo_) (Word192 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word192 where
  {-# INLINABLE compare #-}
  compare (Word192 hi_ lo_) (Word192 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word192 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word192 minBound) minBound
  maxBound = (Word192 maxBound) maxBound
instance Enum Word192 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word192 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word192 (succ hi_)) minBound
      else
          (Word192 hi_) (succ lo_)
  pred (Word192 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word192 (pred hi_)) maxBound
      else
          (Word192 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word192 allZeroes) (toEnum x)
  fromEnum (Word192 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word192 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word192 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word192 (negate hi_)) allZeroes
      else
          (Word192 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word192 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word192 hi_ lo_) (Word192 hi' lo')
    = (Word192 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word192 hi_ lo_) (Word192 hi' lo')
    = (Word192
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word192 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Word192 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word192 where
  {-# INLINE divMod #-}
  toInteger (Word192 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x@(Word192 hi_ lo_) y@(Word192 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word192 allZeroes) t2, (Word192 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word192 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word192 allZeroes) (fromIntegral t2),
                  (Word192 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word192 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word192 allZeroes) z, (Word192 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word192 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word192 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word192 allZeroes) z)) lsb,
                              (Word192 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word192 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word192 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word64))) t2)
                  Word192 hhh hll = (shiftL x) t2
                  v@(Word192 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word192 (fromIntegral t4)) t3
                  t6 = (Word192 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word192 (fromIntegral t8)) t7))
                            ((Word192 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word192 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word192 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word192 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word192 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word192 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word192 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word192 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word64)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word192 hi_ lo_)
    = (Word192 (complement hi_)) (complement lo_)
  xor (Word192 hi_ lo_) (Word192 hi' lo')
    = (Word192 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word192 hi_ lo_) (Word192 hi' lo')
    = (Word192 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word192 hi_ lo_) (Word192 hi' lo')
    = (Word192 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word192 hi_ lo_) x
    = if ((>) y) 0 then
          (Word192
             (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word192 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Word192 hi_ lo_) x
    = (Word192 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word192
             (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               ((shiftR lo_) z))
      else
          (Word192
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
        z = ((-) (finiteBitSize (undefined :: Word192))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word192))) y)
  bit x
    = if ((>=) y) 0 then
          (Word192 (bit y)) allZeroes
      else
          (Word192 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Word192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word192 ((setBit hi_) y)) lo_
      else
          (Word192 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Word192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word192 ((clearBit hi_) y)) lo_
      else
          (Word192 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Word192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word192 ((complementBit hi_) y)) lo_
      else
          (Word192 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Word192 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Word192 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word192 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word64)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word192 where
  type UnsignedWord Word192 = Word192
  type SignedWord Word192 = Int192
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word192 hi_ lo_) = (Int192 (signedWord hi_)) lo_
  unwrappedAdd (Word192 hi_ lo_) (Word192 hi' lo')
    = ((Word192 allZeroes) z, (Word192 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word192 hi_ lo_) (Word192 hi' lo')
    = ((Word192
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word192 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word64)
        z = ((-) (finiteBitSize (undefined :: Word128))) y
  leadingZeroes (Word192 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word64)
  trailingZeroes (Word192 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word128)
  allZeroes = (Word192 allZeroes) allZeroes
  allOnes = (Word192 allOnes) allOnes
  msb = (Word192 msb) allZeroes
  lsb = (Word192 allZeroes) lsb
  testMsb (Word192 hi_ _) = testMsb hi_
  testLsb (Word192 _ lo_) = testLsb lo_
  setMsb (Word192 hi_ lo_) = (Word192 (setMsb hi_)) lo_
  setLsb (Word192 hi_ lo_) = (Word192 hi_) (setLsb lo_)
  clearMsb (Word192 hi_ lo_) = (Word192 (clearMsb hi_)) lo_
  clearLsb (Word192 hi_ lo_) = (Word192 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word192->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Word192 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word192"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Word192 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word192"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Word192 #-}
{-# RULES "fromIntegral/Word192->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Word192 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Word192"
              fromIntegral
                = extendLo :: Word128 -> Word192 #-}
{-# RULES "fromIntegral/Word192->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Word192 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Word192"
              fromIntegral
                = signExtendLo :: Int128 -> Word192 #-}
{-# RULES "fromIntegral/Word192->Word192"
              fromIntegral
                = id :: Word192 -> Word192 #-}
{-# RULES "fromIntegral/Word192->Int192"
              fromIntegral
                = signedWord :: Word192 -> Int192 #-}
{-# RULES "fromIntegral/Word192->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Word192 #-}
{-# RULES "fromIntegral/Word192->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word192 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Word192 #-}
data Int192
  = Int192 {-# UNPACK #-} !Int64 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Int192 where
  type LoWord Int192 = Word128
  type HiWord Int192 = Int64
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int192 _ lo_) = lo_
  hiWord (Int192 hi_ _) = hi_
  fromHiAndLo = Int192
  extendLo x = (Int192 allZeroes) x
  signExtendLo x
    = (Int192 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int192 where
  {-# INLINE (==) #-}
  (==) (Int192 hi_ lo_) (Int192 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int192 where
  {-# INLINABLE compare #-}
  compare (Int192 hi_ lo_) (Int192 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int192 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int192 minBound) minBound
  maxBound = (Int192 maxBound) maxBound
instance Enum Int192 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int192 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int192 (succ hi_)) minBound
      else
          (Int192 hi_) (succ lo_)
  pred (Int192 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int192 (pred hi_)) maxBound
      else
          (Int192 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int192 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int192 allZeroes) (toEnum x)
  fromEnum (Int192 0 lo_) = fromEnum lo_
  fromEnum (Int192 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int192 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int192 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int192 (negate hi_)) allZeroes
      else
          (Int192 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int192 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int192 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int192 hi_ lo_) (Int192 hi' lo')
    = (Int192 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int192 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Int192 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int192 where
  toInteger (Int192 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int192 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int192 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int192 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int192 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int192 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int192 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int64)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int192 hi_ lo_)
    = (Int192 (complement hi_)) (complement lo_)
  xor (Int192 hi_ lo_) (Int192 hi' lo')
    = (Int192 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int192 hi_ lo_) (Int192 hi' lo')
    = (Int192 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int192 hi_ lo_) (Int192 hi' lo')
    = (Int192 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int192 hi_ lo_) x
    = if ((>) y) 0 then
          (Int192 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int192 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Int192 hi_ lo_) x
    = (Int192 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word128)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int192))) y)
  bit x
    = if ((>=) y) 0 then
          (Int192 (bit y)) allZeroes
      else
          (Int192 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Int192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int192 ((setBit hi_) y)) lo_
      else
          (Int192 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Int192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int192 ((clearBit hi_) y)) lo_
      else
          (Int192 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Int192 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int192 ((complementBit hi_) y)) lo_
      else
          (Int192 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Int192 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Int192 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int192 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int64)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int192 where
  type UnsignedWord Int192 = Word192
  type SignedWord Int192 = Int192
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int192 hi_ lo_) = (Word192 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int192 hi_ lo_) (Int192 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int192 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int192 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word192 (unsignedWord hi_)) lo_))
              ((Word192 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int192 allZeroes) allZeroes
  allOnes = (Int192 allOnes) allOnes
  msb = (Int192 msb) allZeroes
  lsb = (Int192 allZeroes) lsb
  testMsb (Int192 hi_ _) = testMsb hi_
  testLsb (Int192 _ lo_) = testLsb lo_
  setMsb (Int192 hi_ lo_) = (Int192 (setMsb hi_)) lo_
  setLsb (Int192 hi_ lo_) = (Int192 hi_) (setLsb lo_)
  clearMsb (Int192 hi_ lo_) = (Int192 (clearMsb hi_)) lo_
  clearLsb (Int192 hi_ lo_) = (Int192 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int192->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Int192 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int192"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Int192 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int192"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Int192 #-}
{-# RULES "fromIntegral/Int192->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Int192 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Int192"
              fromIntegral
                = extendLo :: Word128 -> Int192 #-}
{-# RULES "fromIntegral/Int192->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Int192 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Int192"
              fromIntegral
                = signExtendLo :: Int128 -> Int192 #-}
{-# RULES "fromIntegral/Int192->Int192"
              fromIntegral
                = id :: Int192 -> Int192 #-}
{-# RULES "fromIntegral/Int192->Word192"
              fromIntegral
                = unsignedWord :: Int192 -> Word192 #-}
{-# RULES "fromIntegral/Int192->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int192"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Int192 #-}
{-# RULES "fromIntegral/Int192->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int192 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int192"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Int192 #-}

data Word224
  = Word224 {-# UNPACK #-} !Word96 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Word224 where
  type LoWord Word224 = Word128
  type HiWord Word224 = Word96
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word224 _ lo_) = lo_
  hiWord (Word224 hi_ _) = hi_
  fromHiAndLo = Word224
  extendLo x = (Word224 allZeroes) x
  signExtendLo x
    = (Word224 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word224 where
  {-# INLINE (==) #-}
  (==) (Word224 hi_ lo_) (Word224 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word224 where
  {-# INLINABLE compare #-}
  compare (Word224 hi_ lo_) (Word224 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word224 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word224 minBound) minBound
  maxBound = (Word224 maxBound) maxBound
instance Enum Word224 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word224 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word224 (succ hi_)) minBound
      else
          (Word224 hi_) (succ lo_)
  pred (Word224 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word224 (pred hi_)) maxBound
      else
          (Word224 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word224 allZeroes) (toEnum x)
  fromEnum (Word224 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word224 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word224 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word224 (negate hi_)) allZeroes
      else
          (Word224 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word224 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word224 hi_ lo_) (Word224 hi' lo')
    = (Word224 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word224 hi_ lo_) (Word224 hi' lo')
    = (Word224
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word224 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Word224 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word224 where
  {-# INLINE divMod #-}
  toInteger (Word224 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x@(Word224 hi_ lo_) y@(Word224 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word224 allZeroes) t2, (Word224 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word224 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word224 allZeroes) (fromIntegral t2),
                  (Word224 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word224 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word224 allZeroes) z, (Word224 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word224 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word224 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word224 allZeroes) z)) lsb,
                              (Word224 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word224 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word224 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word96))) t2)
                  Word224 hhh hll = (shiftL x) t2
                  v@(Word224 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word224 (fromIntegral t4)) t3
                  t6 = (Word224 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word224 (fromIntegral t8)) t7))
                            ((Word224 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word224 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word224 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word224 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word224 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word224 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word224 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word224 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word96)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word224 hi_ lo_)
    = (Word224 (complement hi_)) (complement lo_)
  xor (Word224 hi_ lo_) (Word224 hi' lo')
    = (Word224 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word224 hi_ lo_) (Word224 hi' lo')
    = (Word224 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word224 hi_ lo_) (Word224 hi' lo')
    = (Word224 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word224 hi_ lo_) x
    = if ((>) y) 0 then
          (Word224
             (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word224 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Word224 hi_ lo_) x
    = (Word224 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word224
             (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               ((shiftR lo_) z))
      else
          (Word224
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
        z = ((-) (finiteBitSize (undefined :: Word224))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word224))) y)
  bit x
    = if ((>=) y) 0 then
          (Word224 (bit y)) allZeroes
      else
          (Word224 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Word224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word224 ((setBit hi_) y)) lo_
      else
          (Word224 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Word224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word224 ((clearBit hi_) y)) lo_
      else
          (Word224 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Word224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word224 ((complementBit hi_) y)) lo_
      else
          (Word224 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Word224 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Word224 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word224 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word96)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word224 where
  type UnsignedWord Word224 = Word224
  type SignedWord Word224 = Int224
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word224 hi_ lo_) = (Int224 (signedWord hi_)) lo_
  unwrappedAdd (Word224 hi_ lo_) (Word224 hi' lo')
    = ((Word224 allZeroes) z, (Word224 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word224 hi_ lo_) (Word224 hi' lo')
    = ((Word224
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word224 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word96)
        z = ((-) (finiteBitSize (undefined :: Word128))) y
  leadingZeroes (Word224 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word96)
  trailingZeroes (Word224 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word128)
  allZeroes = (Word224 allZeroes) allZeroes
  allOnes = (Word224 allOnes) allOnes
  msb = (Word224 msb) allZeroes
  lsb = (Word224 allZeroes) lsb
  testMsb (Word224 hi_ _) = testMsb hi_
  testLsb (Word224 _ lo_) = testLsb lo_
  setMsb (Word224 hi_ lo_) = (Word224 (setMsb hi_)) lo_
  setLsb (Word224 hi_ lo_) = (Word224 hi_) (setLsb lo_)
  clearMsb (Word224 hi_ lo_) = (Word224 (clearMsb hi_)) lo_
  clearLsb (Word224 hi_ lo_) = (Word224 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word224->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Word224 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word224"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Word224 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word224"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Word224 #-}
{-# RULES "fromIntegral/Word224->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Word224 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Word224"
              fromIntegral
                = extendLo :: Word128 -> Word224 #-}
{-# RULES "fromIntegral/Word224->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Word224 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Word224"
              fromIntegral
                = signExtendLo :: Int128 -> Word224 #-}
{-# RULES "fromIntegral/Word224->Word224"
              fromIntegral
                = id :: Word224 -> Word224 #-}
{-# RULES "fromIntegral/Word224->Int224"
              fromIntegral
                = signedWord :: Word224 -> Int224 #-}
{-# RULES "fromIntegral/Word224->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Word224 #-}
{-# RULES "fromIntegral/Word224->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word224 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Word224 #-}
data Int224
  = Int224 {-# UNPACK #-} !Int96 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Int224 where
  type LoWord Int224 = Word128
  type HiWord Int224 = Int96
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int224 _ lo_) = lo_
  hiWord (Int224 hi_ _) = hi_
  fromHiAndLo = Int224
  extendLo x = (Int224 allZeroes) x
  signExtendLo x
    = (Int224 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int224 where
  {-# INLINE (==) #-}
  (==) (Int224 hi_ lo_) (Int224 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int224 where
  {-# INLINABLE compare #-}
  compare (Int224 hi_ lo_) (Int224 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int224 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int224 minBound) minBound
  maxBound = (Int224 maxBound) maxBound
instance Enum Int224 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int224 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int224 (succ hi_)) minBound
      else
          (Int224 hi_) (succ lo_)
  pred (Int224 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int224 (pred hi_)) maxBound
      else
          (Int224 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int224 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int224 allZeroes) (toEnum x)
  fromEnum (Int224 0 lo_) = fromEnum lo_
  fromEnum (Int224 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int224 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int224 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int224 (negate hi_)) allZeroes
      else
          (Int224 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int224 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int224 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int224 hi_ lo_) (Int224 hi' lo')
    = (Int224 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int224 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Int224 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int224 where
  toInteger (Int224 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int224 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int224 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int224 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int224 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int224 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int224 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int96)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int224 hi_ lo_)
    = (Int224 (complement hi_)) (complement lo_)
  xor (Int224 hi_ lo_) (Int224 hi' lo')
    = (Int224 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int224 hi_ lo_) (Int224 hi' lo')
    = (Int224 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int224 hi_ lo_) (Int224 hi' lo')
    = (Int224 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int224 hi_ lo_) x
    = if ((>) y) 0 then
          (Int224 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int224 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Int224 hi_ lo_) x
    = (Int224 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word128)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int224))) y)
  bit x
    = if ((>=) y) 0 then
          (Int224 (bit y)) allZeroes
      else
          (Int224 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Int224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int224 ((setBit hi_) y)) lo_
      else
          (Int224 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Int224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int224 ((clearBit hi_) y)) lo_
      else
          (Int224 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Int224 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int224 ((complementBit hi_) y)) lo_
      else
          (Int224 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Int224 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Int224 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int224 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int96)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int224 where
  type UnsignedWord Int224 = Word224
  type SignedWord Int224 = Int224
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int224 hi_ lo_) = (Word224 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int224 hi_ lo_) (Int224 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int224 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int224 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word224 (unsignedWord hi_)) lo_))
              ((Word224 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int224 allZeroes) allZeroes
  allOnes = (Int224 allOnes) allOnes
  msb = (Int224 msb) allZeroes
  lsb = (Int224 allZeroes) lsb
  testMsb (Int224 hi_ _) = testMsb hi_
  testLsb (Int224 _ lo_) = testLsb lo_
  setMsb (Int224 hi_ lo_) = (Int224 (setMsb hi_)) lo_
  setLsb (Int224 hi_ lo_) = (Int224 hi_) (setLsb lo_)
  clearMsb (Int224 hi_ lo_) = (Int224 (clearMsb hi_)) lo_
  clearLsb (Int224 hi_ lo_) = (Int224 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int224->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Int224 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int224"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Int224 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int224"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Int224 #-}
{-# RULES "fromIntegral/Int224->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Int224 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Int224"
              fromIntegral
                = extendLo :: Word128 -> Int224 #-}
{-# RULES "fromIntegral/Int224->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Int224 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Int224"
              fromIntegral
                = signExtendLo :: Int128 -> Int224 #-}
{-# RULES "fromIntegral/Int224->Int224"
              fromIntegral
                = id :: Int224 -> Int224 #-}
{-# RULES "fromIntegral/Int224->Word224"
              fromIntegral
                = unsignedWord :: Int224 -> Word224 #-}
{-# RULES "fromIntegral/Int224->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int224"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Int224 #-}
{-# RULES "fromIntegral/Int224->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int224 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int224"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Int224 #-}

data Word256
  = Word256 {-# UNPACK #-} !Word128 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Word256 where
  type LoWord Word256 = Word128
  type HiWord Word256 = Word128
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Word256 _ lo_) = lo_
  hiWord (Word256 hi_ _) = hi_
  fromHiAndLo = Word256
  extendLo x = (Word256 allZeroes) x
  signExtendLo x
    = (Word256 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Word256 where
  {-# INLINE (==) #-}
  (==) (Word256 hi_ lo_) (Word256 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Word256 where
  {-# INLINABLE compare #-}
  compare (Word256 hi_ lo_) (Word256 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Word256 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Word256 minBound) minBound
  maxBound = (Word256 maxBound) maxBound
instance Enum Word256 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Word256 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Word256 (succ hi_)) minBound
      else
          (Word256 hi_) (succ lo_)
  pred (Word256 hi_ lo_)
    = if ((==) lo_) minBound then
          (Word256 (pred hi_)) maxBound
      else
          (Word256 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          error "toEnum: nagative value"
      else
          (Word256 allZeroes) (toEnum x)
  fromEnum (Word256 0 lo_) = fromEnum lo_
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Word256 where
  {-# INLINABLE negate #-}
  {-# INLINE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Word256 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Word256 (negate hi_)) allZeroes
      else
          (Word256 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = x
  signum (Word256 hi_ lo_)
    = if ((&&) (((==) hi_) allZeroes)) (((==) lo_) allZeroes) then
          allZeroes
      else
          lsb
  (+) (Word256 hi_ lo_) (Word256 hi' lo')
    = (Word256 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) (Word256 hi_ lo_) (Word256 hi' lo')
    = (Word256
         (((+)
             (((+) (((*) hi_) (fromIntegral lo')))
                (((*) hi') (fromIntegral lo_))))
            (fromIntegral x)))
        y
    where
        (x, y) = (unwrappedMul lo_) lo'
  fromInteger x
    = (Word256 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Word256 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Word256 where
  {-# INLINE divMod #-}
  toInteger (Word256 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x@(Word256 hi_ lo_) y@(Word256 hi' lo')
    = if ((&&) (((==) hi') allZeroes)) (((==) lo') allZeroes) then
          error "divide by zero"
      else
          case (compare hi_) hi' of
            LT -> (allZeroes, x)
            EQ
              -> case (compare lo_) lo' of
                   LT -> (allZeroes, x)
                   EQ -> (lsb, allZeroes)
                   GT
                     | ((==) hi') allZeroes
                     -> ((Word256 allZeroes) t2, (Word256 allZeroes) t1)
                     where
                         (t2, t1) = (quotRem lo_) lo'
                   GT -> (lsb, (Word256 allZeroes) (((-) lo_) lo'))
            GT
              | ((==) lo') allZeroes
              -> ((Word256 allZeroes) (fromIntegral t2),
                  (Word256 (fromIntegral t1)) lo_)
              where
                  (t2, t1) = (quotRem hi_) hi'
            GT
              | ((&&) (((==) hi') allZeroes)) (((==) lo') maxBound)
              -> if ((==) t2) allZeroes then
                     if ((==) t1) maxBound then
                         (((+) ((Word256 allZeroes) z)) lsb, allZeroes)
                     else
                         ((Word256 allZeroes) z, (Word256 allZeroes) t1)
                 else
                     if ((==) t1) maxBound then
                         (((+) ((Word256 allZeroes) z)) 2, lsb)
                     else
                         if ((==) t1) ((xor maxBound) lsb) then
                             (((+) ((Word256 allZeroes) z)) 2, allZeroes)
                         else
                             (((+) ((Word256 allZeroes) z)) lsb,
                              (Word256 allZeroes) (((+) t1) lsb))
              where
                  z = fromIntegral hi_
                  (t2, t1) = (unwrappedAdd z) lo_
            GT
              | ((==) hi') allZeroes -> (t2, (Word256 allZeroes) t1)
              where
                  (t2, t1) = ((div1 hi_) lo_) lo'
            GT
              -> if ((==) t1) t2 then
                     (lsb, ((-) x) y)
                 else
                     ((Word256 allZeroes) (fromIntegral q2), (shiftR r2) t2)
              where
                  t1 = leadingZeroes hi_
                  t2 = leadingZeroes hi'
                  z = (shiftR hi_) (((-) (finiteBitSize (undefined :: Word128))) t2)
                  Word256 hhh hll = (shiftL x) t2
                  v@(Word256 lhh lll) = (shiftL y) t2
                  ((0, q1), r1) = ((div2 z) hhh) lhh
                  (t4, t3) = (unwrappedMul (fromIntegral q1)) lll
                  t5 = (Word256 (fromIntegral t4)) t3
                  t6 = (Word256 r1) hll
                  (t8, t7) = (unwrappedAdd t6) v
                  (t10, t9) = (unwrappedAdd t7) v
                  (q2, r2)
                    = if ((>) t5) t6 then
                          if ((==) (loWord t8)) allZeroes then
                              if ((>=) t7) t5 then
                                  (((-) q1) lsb, ((-) t7) t5)
                              else
                                  if ((==) (loWord t10)) allZeroes then
                                      (((-) q1) 2, ((-) t9) t5)
                                  else
                                      (((-) q1) 2, ((+) (((-) maxBound) t5)) (((+) t9) lsb))
                          else
                              (((-) q1) lsb, ((+) (((-) maxBound) t5)) (((+) t7) lsb))
                      else
                          (q1, ((-) t6) t5)
    where
        div1 hhh hll by_
          = ((go_ hhh) hll) allZeroes
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      (((+) c)
                         (((+) ((Word256 (fromIntegral t8)) t7))
                            ((Word256 allZeroes) t10)),
                       t9)
                  else
                      ((go_ (fromIntegral z)) t5)
                        (((+) c) ((Word256 (fromIntegral t8)) t7))
                where
                    h1 = fromIntegral h
                    (t4, t3) = (unwrappedMul h1) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h1) t2
                    (t10, t9) = (quotRem t5) by_
        div2 hhh hll by_
          = ((go_ hhh) hll) (allZeroes, allZeroes)
          where
              (t2, t1) = (quotRem maxBound) by_
              go_ h l c
                = if ((==) z) allZeroes then
                      ((addT c) ((addT (t8, t7)) (allZeroes, t10)), t9)
                  else
                      ((go_ z) t5) ((addT c) (t8, t7))
                where
                    (t4, t3) = (unwrappedMul h) (((+) t1) lsb)
                    (t6, t5) = (unwrappedAdd t3) l
                    z = ((+) t4) t6
                    (t8, t7) = (unwrappedMul h) t2
                    (t10, t9) = (quotRem t5) by_
              addT (lhh, lhl) (llh, lll)
                = (((+) t4) (((+) lhh) llh), t3)
                where
                    (t4, t3) = (unwrappedAdd lhl) lll
  divMod = quotRem
instance Show Word256 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Word256 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Word256 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Word256 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Word256 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Word256 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Word128)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = False
  complement (Word256 hi_ lo_)
    = (Word256 (complement hi_)) (complement lo_)
  xor (Word256 hi_ lo_) (Word256 hi' lo')
    = (Word256 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Word256 hi_ lo_) (Word256 hi' lo')
    = (Word256 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Word256 hi_ lo_) (Word256 hi' lo')
    = (Word256 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Word256 hi_ lo_) x
    = if ((>) y) 0 then
          (Word256
             (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Word256 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Word256 hi_ lo_) x
    = (Word256 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = (shiftR (fromIntegral hi_)) (negate y)
  rotateL (Word256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word256
             (((.|.) (fromIntegral ((shiftL lo_) y))) ((shiftR hi_) z)))
            (((.|.)
                ((shiftL (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               ((shiftR lo_) z))
      else
          (Word256
             (((.|.) (fromIntegral ((shiftR lo_) (negate y))))
                ((shiftL hi_) x)))
            (((.|.)
                ((shift (fromIntegral hi_))
                   (((-) (finiteBitSize (undefined :: Word128))) z)))
               (((.|.) ((shiftL lo_) x)) ((shiftR lo_) z)))
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
        z = ((-) (finiteBitSize (undefined :: Word256))) x
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Word256))) y)
  bit x
    = if ((>=) y) 0 then
          (Word256 (bit y)) allZeroes
      else
          (Word256 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Word256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word256 ((setBit hi_) y)) lo_
      else
          (Word256 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Word256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word256 ((clearBit hi_) y)) lo_
      else
          (Word256 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Word256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Word256 ((complementBit hi_) y)) lo_
      else
          (Word256 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Word256 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Word256 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Word256 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Word128)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Word256 where
  type UnsignedWord Word256 = Word256
  type SignedWord Word256 = Int256
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINE leadingZeroes #-}
  {-# INLINE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord = id
  signedWord (Word256 hi_ lo_) = (Int256 (signedWord hi_)) lo_
  unwrappedAdd (Word256 hi_ lo_) (Word256 hi' lo')
    = ((Word256 allZeroes) z, (Word256 y) x)
    where
        (t1, x) = (unwrappedAdd lo_) lo'
        (t3, t2) = (unwrappedAdd hi_) (fromIntegral t1)
        (t4, y) = (unwrappedAdd t2) hi'
        z = fromIntegral (((+) t3) t4)
  unwrappedMul (Word256 hi_ lo_) (Word256 hi' lo')
    = ((Word256
          (((+) hhh) (((+) (fromIntegral ((shiftR t9) y))) ((shiftL x) z))))
         (((.|.) ((shiftL t9) z)) ((shiftR t3) y)),
       (Word256 (fromIntegral t3)) lll)
    where
        (llh, lll) = (unwrappedMul lo_) lo'
        (hlh, hll) = (unwrappedMul (fromIntegral hi_)) lo'
        (lhh, lhl) = (unwrappedMul lo_) (fromIntegral hi')
        (hhh, hhl) = (unwrappedMul hi_) hi'
        (t2, t1) = (unwrappedAdd llh) hll
        (t4, t3) = (unwrappedAdd t1) lhl
        (t6, t5) = (unwrappedAdd (fromIntegral hhl)) (((+) t2) t4)
        (t8, t7) = (unwrappedAdd t5) lhh
        (t10, t9) = (unwrappedAdd t7) hlh
        x = fromIntegral (((+) t6) (((+) t8) t10))
        y = finiteBitSize (undefined :: Word128)
        z = ((-) (finiteBitSize (undefined :: Word128))) y
  leadingZeroes (Word256 hi_ lo_)
    = if ((==) x) y then ((+) y) (leadingZeroes lo_) else x
    where
        x = leadingZeroes hi_
        y = finiteBitSize (undefined :: Word128)
  trailingZeroes (Word256 hi_ lo_)
    = if ((==) x) y then ((+) y) (trailingZeroes hi_) else x
    where
        x = trailingZeroes lo_
        y = finiteBitSize (undefined :: Word128)
  allZeroes = (Word256 allZeroes) allZeroes
  allOnes = (Word256 allOnes) allOnes
  msb = (Word256 msb) allZeroes
  lsb = (Word256 allZeroes) lsb
  testMsb (Word256 hi_ _) = testMsb hi_
  testLsb (Word256 _ lo_) = testLsb lo_
  setMsb (Word256 hi_ lo_) = (Word256 (setMsb hi_)) lo_
  setLsb (Word256 hi_ lo_) = (Word256 hi_) (setLsb lo_)
  clearMsb (Word256 hi_ lo_) = (Word256 (clearMsb hi_)) lo_
  clearLsb (Word256 hi_ lo_) = (Word256 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Word256->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Word256 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Word256"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Word256 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Word256"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Word256 #-}
{-# RULES "fromIntegral/Word256->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Word256 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Word256"
              fromIntegral
                = extendLo :: Word128 -> Word256 #-}
{-# RULES "fromIntegral/Word256->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Word256 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Word256"
              fromIntegral
                = signExtendLo :: Int128 -> Word256 #-}
{-# RULES "fromIntegral/Word256->Word256"
              fromIntegral
                = id :: Word256 -> Word256 #-}
{-# RULES "fromIntegral/Word256->Int256"
              fromIntegral
                = signedWord :: Word256 -> Int256 #-}
{-# RULES "fromIntegral/Word256->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Word256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Word256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Word256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Word256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Word256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Word256 #-}
{-# RULES "fromIntegral/Word256->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Word256 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Word256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Word256 #-}
data Int256
  = Int256 {-# UNPACK #-} !Int128 {-# UNPACK #-} !Word128
  deriving (Typeable, Data, Generic)
instance DoubleWord Int256 where
  type LoWord Int256 = Word128
  type HiWord Int256 = Int128
  {-# INLINE loWord #-}
  {-# INLINE hiWord #-}
  {-# INLINE fromHiAndLo #-}
  {-# INLINE extendLo #-}
  {-# INLINABLE signExtendLo #-}
  loWord (Int256 _ lo_) = lo_
  hiWord (Int256 hi_ _) = hi_
  fromHiAndLo = Int256
  extendLo x = (Int256 allZeroes) x
  signExtendLo x
    = (Int256 (if testMsb x then allOnes else allZeroes))
        (unsignedWord x)
instance Eq Int256 where
  {-# INLINE (==) #-}
  (==) (Int256 hi_ lo_) (Int256 hi' lo')
    = ((&&) (((==) hi_) hi')) (((==) lo_) lo')
instance Ord Int256 where
  {-# INLINABLE compare #-}
  compare (Int256 hi_ lo_) (Int256 hi' lo')
    = case (compare hi_) hi' of
        EQ -> (compare lo_) lo'
        x -> x
instance Bounded Int256 where
  {-# INLINE minBound #-}
  {-# INLINE maxBound #-}
  minBound = (Int256 minBound) minBound
  maxBound = (Int256 maxBound) maxBound
instance Enum Int256 where
  {-# INLINABLE succ #-}
  {-# INLINABLE pred #-}
  {-# INLINE enumFrom #-}
  {-# INLINABLE enumFromThen #-}
  succ (Int256 hi_ lo_)
    = if ((==) lo_) maxBound then
          (Int256 (succ hi_)) minBound
      else
          (Int256 hi_) (succ lo_)
  pred (Int256 hi_ lo_)
    = if ((==) lo_) minBound then
          (Int256 (pred hi_)) maxBound
      else
          (Int256 hi_) (pred lo_)
  toEnum x
    = if ((<) x) 0 then
          (Int256 allOnes) (negate (((+) lsb) (toEnum (negate (((+) x) 1)))))
      else
          (Int256 allZeroes) (toEnum x)
  fromEnum (Int256 0 lo_) = fromEnum lo_
  fromEnum (Int256 (-1) lo_) = negate (fromEnum (negate lo_))
  fromEnum _ = error "fromEnum: out of bounds"
  enumFrom x = (enumFromTo x) maxBound
  enumFromThen x y
    = ((enumFromThenTo x) y)
        (if ((>=) y) x then maxBound else minBound)
  enumFromTo x y
    = case (compare y) x of
        LT -> []
        EQ -> ((:) x) []
        GT -> ((:) x) ((up_ y) x)
    where
        up_ to_ c
          = ((:) next_) (if ((==) next_) to_ then [] else (up_ to_) next_)
          where
              next_ = ((+) c) lsb
  enumFromThenTo x y z
    = case (compare y) x of
        LT
          -> if ((>) z) y then
                 if ((>) z) x then [] else ((:) x) []
             else
                 ((:) x) (down_ y)
          where
              step_ = ((-) x) y
              to_ = ((+) z) step_
              down_ c
                = if ((<) c) to_ then
                      ((:) c) []
                  else
                      ((:) c) (down_ (((-) c) step_))
        EQ -> if ((<) z) x then [] else repeat x
        GT
          -> if ((<) z) y then
                 if ((<) z) x then [] else ((:) x) []
             else
                 ((:) x) (up_ y)
          where
              step_ = ((-) y) x
              to_ = ((-) z) step_
              up_ c
                = if ((>) c) to_ then ((:) c) [] else ((:) c) (up_ (((+) c) step_))
instance Num Int256 where
  {-# INLINABLE negate #-}
  {-# INLINABLE abs #-}
  {-# INLINABLE signum #-}
  {-# INLINABLE (+) #-}
  {-# INLINABLE (*) #-}
  negate (Int256 hi_ lo_)
    = if ((==) lo_) allZeroes then
          (Int256 (negate hi_)) allZeroes
      else
          (Int256 (negate (((+) lsb) hi_))) (negate lo_)
  abs x = if ((<) x) allZeroes then negate x else x
  signum (Int256 hi_ lo_)
    = case (compare hi_) allZeroes of
        LT -> (Int256 allOnes) maxBound
        EQ -> if ((==) lo_) allZeroes then allZeroes else lsb
        GT -> lsb
  (+) (Int256 hi_ lo_) (Int256 hi' lo')
    = (Int256 y) x
    where
        x = ((+) lo_) lo'
        y = ((+) (((+) hi_) hi')) (if ((<) x) lo_ then lsb else allZeroes)
  (*) x y = signedWord (((*) (unsignedWord x)) (unsignedWord y))
  fromInteger x
    = (Int256 (fromInteger y)) (fromInteger z)
    where
        (y, z) = (divMod x) (((+) (toInteger (maxBound :: Word128))) 1)
instance Real Int256 where
  {-# INLINE toRational #-}
  toRational x = ((%) (toInteger x)) 1
instance Integral Int256 where
  toInteger (Int256 hi_ lo_)
    = ((+)
         (((*) (toInteger hi_))
            (((+) (toInteger (maxBound :: Word128))) 1)))
        (toInteger lo_)
  quotRem x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
              in (signedWord (negate q), signedWord (negate r))
      else
          if testMsb y then
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
              in (signedWord (negate q), signedWord r)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
  divMod x y
    = if testMsb x then
          if testMsb y then
              let
                (q, r)
                  = (quotRem (unsignedWord (negate x))) (unsignedWord (negate y))
              in (signedWord q, signedWord (negate r))
          else
              let
                (q, r) = (quotRem (unsignedWord (negate x))) (unsignedWord y)
                q1 = signedWord (negate q)
                r1 = signedWord (negate r)
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
      else
          if testMsb y then
              let
                (q, r) = (quotRem (unsignedWord x)) (unsignedWord (negate y))
                q1 = signedWord (negate q)
                r1 = signedWord r
              in
                if ((==) r) allZeroes then (q1, r1) else (((-) q1) lsb, ((+) r1) y)
          else
              let (q, r) = (quotRem (unsignedWord x)) (unsignedWord y)
              in (signedWord q, signedWord r)
instance Show Int256 where
  {-# INLINE show #-}
  show = ((.) show) toInteger
instance Read Int256 where
  readsPrec x y
    = (fmap (\ (q, r) -> (fromInteger q, r))) ((readsPrec x) y)
instance Hashable Int256 where
  {-# INLINE hashWithSalt #-}
  hashWithSalt x (Int256 hi_ lo_)
    = (hashWithSalt ((hashWithSalt x) hi_)) lo_
instance Ix Int256 where
  {-# INLINE range #-}
  {-# INLINE unsafeIndex #-}
  {-# INLINE inRange #-}
  range (x, y) = (enumFromTo x) y
  unsafeIndex (x, _) z = ((-) (fromIntegral z)) (fromIntegral x)
  inRange (x, y) z = ((&&) (((>=) z) x)) (((<=) z) y)
instance Bits Int256 where
  {-# INLINE bitSize #-}
  {-# INLINE bitSizeMaybe #-}
  {-# INLINE isSigned #-}
  {-# INLINE complement #-}
  {-# INLINE xor #-}
  {-# INLINE (.&.) #-}
  {-# INLINE (.|.) #-}
  {-# INLINE rotateR #-}
  {-# INLINABLE bit #-}
  {-# INLINABLE setBit #-}
  {-# INLINABLE clearBit #-}
  {-# INLINABLE complementBit #-}
  {-# INLINABLE testBit #-}
  {-# INLINE popCount #-}
  {-# INLINE rotateL #-}
  bitSize _
    = ((+) (finiteBitSize (undefined :: Int128)))
        (finiteBitSize (undefined :: Word128))
  bitSizeMaybe = ((.) Just) finiteBitSize
  isSigned _ = True
  complement (Int256 hi_ lo_)
    = (Int256 (complement hi_)) (complement lo_)
  xor (Int256 hi_ lo_) (Int256 hi' lo')
    = (Int256 ((xor hi_) hi')) ((xor lo_) lo')
  (.&.) (Int256 hi_ lo_) (Int256 hi' lo')
    = (Int256 (((.&.) hi_) hi')) (((.&.) lo_) lo')
  (.|.) (Int256 hi_ lo_) (Int256 hi' lo')
    = (Int256 (((.|.) hi_) hi')) (((.|.) lo_) lo')
  shiftL (Int256 hi_ lo_) x
    = if ((>) y) 0 then
          (Int256 (((.|.) ((shiftL hi_) x)) (fromIntegral ((shiftR lo_) y))))
            ((shiftL lo_) x)
      else
          (Int256 (fromIntegral ((shiftL lo_) (negate y)))) allZeroes
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
  shiftR (Int256 hi_ lo_) x
    = (Int256 ((shiftR hi_) x))
        (if ((>=) y) 0 then
             ((.|.) ((shiftL (fromIntegral hi_)) y)) ((shiftR lo_) x)
         else
             z)
    where
        y = ((-) (finiteBitSize (undefined :: Word128))) x
        z = fromIntegral
              ((shiftR (fromIntegral hi_ :: SignedWord Word128)) (negate y))
  rotateL x y = signedWord ((rotateL (unsignedWord x)) y)
  rotateR x y
    = (rotateL x) (((-) (finiteBitSize (undefined :: Int256))) y)
  bit x
    = if ((>=) y) 0 then
          (Int256 (bit y)) allZeroes
      else
          (Int256 allZeroes) (bit x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  setBit (Int256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int256 ((setBit hi_) y)) lo_
      else
          (Int256 hi_) ((setBit lo_) x)
    where
        y = ((-) x) (bitSize (undefined :: Word128))
  clearBit (Int256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int256 ((clearBit hi_) y)) lo_
      else
          (Int256 hi_) ((clearBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  complementBit (Int256 hi_ lo_) x
    = if ((>=) y) 0 then
          (Int256 ((complementBit hi_) y)) lo_
      else
          (Int256 hi_) ((complementBit lo_) x)
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  testBit (Int256 hi_ lo_) x
    = if ((>=) y) 0 then (testBit hi_) y else (testBit lo_) x
    where
        y = ((-) x) (finiteBitSize (undefined :: Word128))
  popCount (Int256 hi_ lo_) = ((+) (popCount hi_)) (popCount lo_)
instance FiniteBits Int256 where
  {-# INLINE finiteBitSize #-}
  {-# INLINE countLeadingZeros #-}
  {-# INLINE countTrailingZeros #-}
  finiteBitSize _
    = ((+) (finiteBitSize (undefined :: Int128)))
        (finiteBitSize (undefined :: Word128))
  countLeadingZeros = leadingZeroes
  countTrailingZeros = trailingZeroes
instance BinaryWord Int256 where
  type UnsignedWord Int256 = Word256
  type SignedWord Int256 = Int256
  {-# INLINE unsignedWord #-}
  {-# INLINE signedWord #-}
  {-# INLINABLE leadingZeroes #-}
  {-# INLINABLE trailingZeroes #-}
  {-# INLINE allZeroes #-}
  {-# INLINE allOnes #-}
  {-# INLINE msb #-}
  {-# INLINE lsb #-}
  {-# INLINE testMsb #-}
  {-# INLINE testLsb #-}
  {-# INLINE setMsb #-}
  {-# INLINE setLsb #-}
  {-# INLINE clearMsb #-}
  {-# INLINE clearLsb #-}
  unsignedWord (Int256 hi_ lo_) = (Word256 (unsignedWord hi_)) lo_
  signedWord = id
  unwrappedAdd x y
    = (z, t4)
    where
        t1 = if testMsb x then maxBound else minBound
        t2 = if testMsb y then maxBound else minBound
        (t3, t4) = (unwrappedAdd (unsignedWord x)) (unsignedWord y)
        z = signedWord (((+) t1) (((+) t2) t3))
  unwrappedMul (Int256 hi_ lo_) (Int256 hi' lo')
    = (x, y)
    where
        t1 = ((+) ((Int256 (complement hi')) (complement lo'))) lsb
        t2 = ((+) ((Int256 (complement hi_)) (complement lo_))) lsb
        (t3, y)
          = (unwrappedMul ((Word256 (unsignedWord hi_)) lo_))
              ((Word256 (unsignedWord hi')) lo')
        z = signedWord t3
        x = if testMsb hi_ then
                if testMsb hi' then ((+) z) (((+) t1) t2) else ((+) z) t1
            else
                if testMsb hi' then ((+) z) t2 else z
  leadingZeroes = ((.) leadingZeroes) unsignedWord
  trailingZeroes = ((.) trailingZeroes) unsignedWord
  allZeroes = (Int256 allZeroes) allZeroes
  allOnes = (Int256 allOnes) allOnes
  msb = (Int256 msb) allZeroes
  lsb = (Int256 allZeroes) lsb
  testMsb (Int256 hi_ _) = testMsb hi_
  testLsb (Int256 _ lo_) = testLsb lo_
  setMsb (Int256 hi_ lo_) = (Int256 (setMsb hi_)) lo_
  setLsb (Int256 hi_ lo_) = (Int256 hi_) (setLsb lo_)
  clearMsb (Int256 hi_ lo_) = (Int256 (clearMsb hi_)) lo_
  clearLsb (Int256 hi_ lo_) = (Int256 hi_) (clearLsb lo_)
{-# RULES "fromIntegral/Int256->GHC.Word.Word64"
              fromIntegral
                = ((.) loWord) loWord :: Int256 -> Word64 #-}
{-# RULES "fromIntegral/GHC.Word.Word64->Int256"
              fromIntegral
                = ((.) extendLo) extendLo :: Word64 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Int.Int64"
              fromIntegral
                = ((.) signedWord) (((.) loWord) loWord) :: Int256 -> Int64 #-}
{-# RULES "fromIntegral/GHC.Int.Int64->Int256"
              fromIntegral
                = ((.) signExtendLo) signExtendLo :: Int64 -> Int256 #-}
{-# RULES "fromIntegral/Int256->Data.DoubleWord.Word128"
              fromIntegral
                = loWord :: Int256 -> Word128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Word128->Int256"
              fromIntegral
                = extendLo :: Word128 -> Int256 #-}
{-# RULES "fromIntegral/Int256->Data.DoubleWord.Int128"
              fromIntegral
                = ((.) signedWord) loWord :: Int256 -> Int128 #-}
{-# RULES "fromIntegral/Data.DoubleWord.Int128->Int256"
              fromIntegral
                = signExtendLo :: Int128 -> Int256 #-}
{-# RULES "fromIntegral/Int256->Int256"
              fromIntegral
                = id :: Int256 -> Int256 #-}
{-# RULES "fromIntegral/Int256->Word256"
              fromIntegral
                = unsignedWord :: Int256 -> Word256 #-}
{-# RULES "fromIntegral/Int256->GHC.Word.Word32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Word32 #-}
{-# RULES "fromIntegral/GHC.Word.Word32->Int256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word32 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Int.Int32"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Int32 #-}
{-# RULES "fromIntegral/GHC.Int.Int32->Int256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int32 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Word.Word16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Word16 #-}
{-# RULES "fromIntegral/GHC.Word.Word16->Int256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word16 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Int.Int16"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Int16 #-}
{-# RULES "fromIntegral/GHC.Int.Int16->Int256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int16 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Word.Word8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Word8 #-}
{-# RULES "fromIntegral/GHC.Word.Word8->Int256"
              fromIntegral
                = ((.) (((.) extendLo) extendLo)) fromIntegral ::
                    Word8 -> Int256 #-}
{-# RULES "fromIntegral/Int256->GHC.Int.Int8"
              fromIntegral
                = ((.) fromIntegral) (((.) loWord) loWord) :: Int256 -> Int8 #-}
{-# RULES "fromIntegral/GHC.Int.Int8->Int256"
              fromIntegral
                = ((.) (((.) signExtendLo) signExtendLo)) fromIntegral ::
                    Int8 -> Int256 #-}

