{-# LANGUAGE PatternSynonyms #-}

module Data.LLVM.BitCode.BitString
  (
    BitString
  , emptyBitString
  , toBitString
  , showBitString
  , fromBitString
  , bitStringValue
  , take, drop
  , joinBitString
  , NumBits, NumBytes, pattern Bits', pattern Bytes'
  , bitCount, bitsToBytes, bytesToBits
  , addBitCounts
  , subtractBitCounts
  )
where

import Data.Bits ((.&.),(.|.),shiftL,shiftR,bit,bitSizeMaybe, Bits)
import Numeric ( showIntAtBase, showHex )

import Prelude hiding (take,drop,splitAt)

----------------------------------------------------------------------
-- Define some convenience newtypes to clarify whether the count of bits or count
-- of bytes is being referenced, and to convert between the two.

newtype NumBits = NumBits Int deriving (Show, Eq, Ord)
newtype NumBytes = NumBytes Int deriving (Show, Eq, Ord)

pattern Bits' :: Int -> NumBits
pattern Bits' n = NumBits n
{-# COMPLETE Bits' #-}

pattern Bytes' :: Int -> NumBytes
pattern Bytes' n = NumBytes n
{-# COMPLETE Bytes' #-}

bitCount :: NumBits -> Int
bitCount (NumBits n) = n

{-# INLINE addBitCounts #-}
addBitCounts :: NumBits -> NumBits -> NumBits
addBitCounts (NumBits a) (NumBits b) = NumBits $ a + b

{-# INLINE subtractBitCounts #-}
subtractBitCounts :: NumBits -> NumBits -> NumBits
subtractBitCounts (NumBits a) (NumBits b) = NumBits $ a - b

{-# INLINE bytesToBits #-}
bitsToBytes :: NumBits -> (NumBytes, NumBits)
bitsToBytes (NumBits n) = (NumBytes $ n `shiftR` 3, NumBits $ n .&. 7)

{-# INLINE bitsToBytes #-}
bytesToBits :: NumBytes -> NumBits
bytesToBits (NumBytes n) = NumBits $ n `shiftL` 3

----------------------------------------------------------------------

data BitString = BitString
  { bsLength :: !NumBits
  , bsData   :: !Int
    -- Note: the bsData was originally an Integer, which allows an essentially
    -- unlimited size value.  However, this adds some overhead to various
    -- computations, and since LLVM Bitcode is unlikely to ever represent values
    -- > native size (64 bits) as discrete values.  By changing this to @Int@,
    -- the use of uboxed calculations is enabled for better performance.
    --
    -- The use of Int is potentially unsound because GHC only guarantees it's a
    -- signed 32-bit integer.  However current implementation in all environments
    -- where it's reasonable to use this parser have a 64-bit Int
    -- implementatinon.  This can be verified via:
    --
    --  > import Data.Bits
    --  > bitSizeMaybe (maxBound :: Int) >= Just 64
    --
    -- There's no good location here to automate this check (perhaps
    -- GetBits.hs:runGetBits?), which is why it isn't verified at runtime.
  } deriving (Show, Eq)

-- | Create an empty BitString

emptyBitString :: BitString
emptyBitString = BitString (NumBits 0) 0


-- | Join two BitString representations together to form a single larger
-- BitString.  The first BitString is the \"lower\" value portion of the resulting
-- BitString.

joinBitString :: BitString -> BitString -> BitString
joinBitString a b =
  let bitSizeA = bitCount $ bsLength a
  in BitString { bsLength = addBitCounts (bsLength a) (bsLength b)
               , bsData = bsData a .|. (bsData b `shiftL` bitSizeA)
               }


-- | Given a number of bits to take, and an @Integer@, create a @BitString@.

toBitString :: NumBits -> Int -> BitString
toBitString len val = BitString len (val .&. maskBits len)


-- | Extract the referenced Integer value from a BitString

bitStringValue :: BitString -> Int
bitStringValue = bsData


-- | Extract a target (Num) value of the desired type from a BitString (using
-- fromInteger to perform the target type conversion).

fromBitString :: (Num a, Bits a) => BitString -> a
fromBitString (BitString l i) =
  case bitSizeMaybe x of
    Nothing -> x
    Just n
      -- Verify that the bitstring size is less than the target size, or if it is
      -- greater, that the extra upper bits are all zero.
      | n >= bitCount l || (ival < bit n) -> x
      | otherwise -> error (unwords
           [ "Data.LLVM.BitCode.BitString.fromBitString: bitstring value of length", show l
           , "(mask=0x" <> showHex i ")"
           , "could not be parsed into type with only", show n, "bits"
           ])
 where
 x    = fromInteger ival  -- use Num's conversion
 ival = toInteger i


showBitString :: BitString -> ShowS
showBitString bs = showString padding . showString bin
  where
  bin     = showIntAtBase 2 fmt (bsData bs) ""
  padding = replicate (bitCount (bsLength bs) - length bin) '0'
  fmt 0   = '0'
  fmt 1   = '1'
  fmt _   = error "invalid binary digit value"


-- | Generate a mask from a number of bits desired.
maskBits :: NumBits -> Int
maskBits (NumBits len)
  | len <= 0  = 0
  | otherwise = pred (bit len)


-- | Extract a smaller BitString with the specified number of bits from the
-- \"start\" of a larger BitString.
take :: NumBits -> BitString -> BitString
take n bs@(BitString l i)
  | n >= l    = bs
  | otherwise = toBitString n i


-- | Remove the specified number of bits from the beginning of a BitString and
-- return the remaining as a smaller BitString.

drop :: NumBits -> BitString -> BitString
drop n (BitString l i)
  | n >= l    = emptyBitString
  | otherwise = BitString
                (NumBits $ bitCount l - bitCount n)
                (i `shiftR` (bitCount n))
