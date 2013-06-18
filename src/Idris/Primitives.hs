{-# LANGUAGE RankNTypes, ScopedTypeVariables, PatternGuards #-}

module Idris.Primitives(elabPrims) where

import Idris.ElabDecls
import Idris.ElabTerm
import Idris.AbsSyntax

import IRTS.Lang

import Core.TT
import Core.Evaluate
import Data.Bits
import Data.Word
import Data.Int
import qualified Data.Vector.Unboxed as V

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Value] -> Maybe Value,
		   p_lexp  :: (Int, PrimFn),
                   p_total :: Totality
                 }

ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

believeTy = Bind (UN "a") (Pi (TType (UVar (-2))))
            (Bind (UN "b") (Pi (TType (UVar (-2))))
            (Bind (UN "x") (Pi (V 1)) (V 1)))

total = Total []
partial = Partial NotCovering 

primitives =
   -- operators
  [Prim (UN "prim__eqChar")  (ty [ChType, ChType] (AType (ATInt ITNative))) 2 (bcBin (==))
     (2, LEq (ATInt ITNative)) total,
   Prim (UN "prim__ltChar")  (ty [ChType, ChType] (AType (ATInt ITNative))) 2 (bcBin (<))
     (2, LLt (ATInt ITNative)) total,
   Prim (UN "prim__lteChar") (ty [ChType, ChType] (AType (ATInt ITNative))) 2 (bcBin (<=))
     (2, LLe (ATInt ITNative)) total,
   Prim (UN "prim__gtChar")  (ty [ChType, ChType] (AType (ATInt ITNative))) 2 (bcBin (>))
     (2, LGt (ATInt ITNative)) total,
   Prim (UN "prim__gteChar") (ty [ChType, ChType] (AType (ATInt ITNative))) 2 (bcBin (>=))
     (2, LGe (ATInt ITNative)) total,

   iCoerce (ITFixed IT8) (ITFixed IT16) "zext" zext LZExt,
   iCoerce (ITFixed IT8) (ITFixed IT32) "zext" zext LZExt,
   iCoerce (ITFixed IT8) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT8) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT8) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT16) (ITFixed IT32) "zext" zext LZExt,
   iCoerce (ITFixed IT16) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT16) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT16) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT32) (ITFixed IT64) "zext" zext LZExt,
   iCoerce (ITFixed IT32) ITBig "zext" zext LZExt,
   iCoerce (ITFixed IT32) ITNative "zext" zext LZExt,
   iCoerce (ITFixed IT64) ITBig "zext" zext LZExt,
   iCoerce ITNative ITBig "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT64) "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT32) "zext" zext LZExt,
   iCoerce ITNative (ITFixed IT16) "zext" zext LZExt,

   iCoerce (ITFixed IT8) (ITFixed IT16) "sext" sext LSExt,
   iCoerce (ITFixed IT8) (ITFixed IT32) "sext" sext LSExt,
   iCoerce (ITFixed IT8) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT8) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT8) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT16) (ITFixed IT32) "sext" sext LSExt,
   iCoerce (ITFixed IT16) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT16) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT16) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT32) (ITFixed IT64) "sext" sext LSExt,
   iCoerce (ITFixed IT32) ITBig "sext" sext LSExt,
   iCoerce (ITFixed IT32) ITNative "sext" sext LSExt,
   iCoerce (ITFixed IT64) ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative ITBig "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT64) "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT32) "sext" sext LSExt,
   iCoerce ITNative (ITFixed IT16) "sext" sext LSExt,

   iCoerce (ITFixed IT16) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT8) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT16) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT32) "trunc" trunc LTrunc,
   iCoerce ITBig (ITFixed IT64) "trunc" trunc LTrunc,
   iCoerce (ITFixed IT16) ITNative "trunc" trunc LTrunc,
   iCoerce (ITFixed IT32) ITNative "trunc" trunc LTrunc,
   iCoerce (ITFixed IT64) ITNative "trunc" trunc LTrunc,
   iCoerce ITBig ITNative "trunc" trunc LTrunc,
   iCoerce ITNative (ITFixed IT64) "trunc" trunc LTrunc,

   Prim (UN "prim__addFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (+))
     (2, LPlus ATFloat) total,
   Prim (UN "prim__subFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (-))
     (2, LMinus ATFloat) total,
   Prim (UN "prim__mulFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (*))
     (2, LTimes ATFloat) total,
   Prim (UN "prim__divFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType ATFloat)) 2 (fBin (/))
     (2, LSDiv ATFloat) total,
   Prim (UN "prim__eqFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (==))
     (2, LEq ATFloat) total,
   Prim (UN "prim__ltFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (<))
     (2, LLt ATFloat) total,
   Prim (UN "prim__lteFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (<=))
     (2, LLe ATFloat) total,
   Prim (UN "prim__gtFloat")  (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (>))
     (2, LGt ATFloat) total,
   Prim (UN "prim__gteFloat") (ty [(AType ATFloat), (AType ATFloat)] (AType (ATInt ITNative))) 2 (bfBin (>=))
     (2, LGe ATFloat) total,
   Prim (UN "prim__concat") (ty [StrType, StrType] StrType) 2 (sBin (++))
    (2, LStrConcat) total,
   Prim (UN "prim__eqString") (ty [StrType, StrType] (AType (ATInt ITNative))) 2 (bsBin (==))
    (2, LStrEq) total,
   Prim (UN "prim__ltString") (ty [StrType, StrType] (AType (ATInt ITNative))) 2 (bsBin (<))
    (2, LStrLt) total,
   Prim (UN "prim_lenString") (ty [StrType] (AType (ATInt ITNative))) 1 (p_strLen)
    (1, LStrLen) total,
    -- Conversions
   Prim (UN "prim__charToInt") (ty [ChType] (AType (ATInt ITNative))) 1 (c_charToInt)
     (1, LChInt ITNative) total,
   Prim (UN "prim__intToChar") (ty [(AType (ATInt ITNative))] ChType) 1 (c_intToChar)
     (1, LIntCh ITNative) total,
   Prim (UN "prim__strToFloat") (ty [StrType] (AType ATFloat)) 1 (c_strToFloat)
     (1, LStrFloat) total,
   Prim (UN "prim__floatToStr") (ty [(AType ATFloat)] StrType) 1 (c_floatToStr)
     (1, LFloatStr) total,

   Prim (UN "prim__floatExp") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatExp)
     (1, LFExp) total, 
   Prim (UN "prim__floatLog") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatLog)
     (1, LFLog) total,
   Prim (UN "prim__floatSin") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatSin)
     (1, LFSin) total,
   Prim (UN "prim__floatCos") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatCos)
     (1, LFCos) total,
   Prim (UN "prim__floatTan") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatTan)
     (1, LFTan) total,
   Prim (UN "prim__floatASin") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatASin)
     (1, LFASin) total,
   Prim (UN "prim__floatACos") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatACos)
     (1, LFACos) total,
   Prim (UN "prim__floatATan") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatATan)
     (1, LFATan) total,
   Prim (UN "prim__floatSqrt") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatSqrt)
     (1, LFSqrt) total,
   Prim (UN "prim__floatFloor") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatFloor)
     (1, LFFloor) total,
   Prim (UN "prim__floatCeil") (ty [(AType ATFloat)] (AType ATFloat)) 1 (p_floatCeil)
     (1, LFCeil) total,

   Prim (UN "prim__strHead") (ty [StrType] ChType) 1 (p_strHead)
     (1, LStrHead) partial,
   Prim (UN "prim__strTail") (ty [StrType] StrType) 1 (p_strTail)
     (1, LStrTail) partial,
   Prim (UN "prim__strCons") (ty [ChType, StrType] StrType) 2 (p_strCons)
    (2, LStrCons) total,
   Prim (UN "prim__strIndex") (ty [StrType, (AType (ATInt ITNative))] ChType) 2 (p_strIndex)
    (2, LStrIndex) partial,
   Prim (UN "prim__strRev") (ty [StrType] StrType) 1 (p_strRev)
    (1, LStrRev) total,
   Prim (UN "prim__readString") (ty [PtrType] StrType) 1 (p_cantreduce)
     (1, LReadStr) partial,
   Prim (UN "prim__vm") (ty [] PtrType) 0 (p_cantreduce)
     (0, LVMPtr) total,
   -- Streams
   Prim (UN "prim__stdin") (ty [] PtrType) 0 (p_cantreduce)
    (0, LStdIn) partial,
   Prim (UN "prim__believe_me") believeTy 3 (p_believeMe)
    (3, LNoOp) partial -- ahem
  ] ++ concatMap intOps [ITFixed IT8, ITFixed IT16, ITFixed IT32, ITFixed IT64, ITBig, ITNative]
    ++ concatMap vecOps [ITVec IT8 16, ITVec IT16 8, ITVec IT32 4, ITVec IT64 2]

intOps ity = intCmps ity ++ intArith ity ++ intConv ity

intCmps ity =
    [ iCmp ity "lt" (bCmp ity (<)) (LLt . ATInt) total
    , iCmp ity "lte" (bCmp ity (<=)) (LLe . ATInt) total
    , iCmp ity "eq" (bCmp ity (==)) (LEq . ATInt) total
    , iCmp ity "gte" (bCmp ity (>=)) (LGe . ATInt) total
    , iCmp ity "gt" (bCmp ity (>)) (LGt . ATInt) total
    ]

intArith ity =
    [ iBinOp ity "add" (bitBin ity (+)) (LPlus . ATInt) total
    , iBinOp ity "sub" (bitBin ity (-)) (LMinus . ATInt) total
    , iBinOp ity "mul" (bitBin ity (*)) (LTimes . ATInt) total
    , iBinOp ity "udiv" (bitBin ity div) LUDiv partial
    , iBinOp ity "sdiv" (bsdiv ity) (LSDiv . ATInt) partial
    , iBinOp ity "urem" (bitBin ity rem) LURem partial
    , iBinOp ity "srem" (bsrem ity) (LSRem . ATInt) partial
    , iBinOp ity "shl" (bitBin ity (\x y -> shiftL x (fromIntegral y))) LSHL total
    , iBinOp ity "lshr" (bitBin ity (\x y -> shiftR x (fromIntegral y))) LLSHR total
    , iBinOp ity "ashr" (bashr ity) LASHR total
    , iBinOp ity "and" (bitBin ity (.&.)) LAnd total
    , iBinOp ity "or" (bitBin ity (.|.)) LOr total
    , iBinOp ity "xor" (bitBin ity (xor)) LXOr total
    , iUnOp ity "compl" (bUn ity complement) LCompl total
    ]

intConv ity =
    [ Prim (UN $ "prim__toStr" ++ intTyName ity) (ty [AType . ATInt $ ity] StrType) 1 intToStr
               (1, LIntStr ity) total
    , Prim (UN $ "prim__fromStr" ++ intTyName ity) (ty [StrType] (AType . ATInt $ ity)) 1 (strToInt ity)
               (1, LStrInt ity) total
    , Prim (UN $ "prim__toFloat" ++ intTyName ity) (ty [AType . ATInt $ ity] (AType ATFloat)) 1 intToFloat
               (1, LIntFloat ity) total
    , Prim (UN $ "prim__fromFloat" ++ intTyName ity) (ty [AType ATFloat] (AType . ATInt $ ity)) 1 (floatToInt ity)
               (1, LFloatInt ity) total
    ]

vecOps ity@(ITVec elem count) =
    [ Prim (UN $ "prim__mk" ++ intTyName ity)
               (ty (replicate count . AType . ATInt . ITFixed $ elem) (AType . ATInt $ ity))
               count (mkVecCon elem count) (count, LMkVec elem count) total
    ] ++ intArith ity

mkVecCon ity count args = if length ints == count
                          then Just $ VConstant (mkVec ity count ints)
                          else Nothing
    where
      ints = getInt args
      mkVec :: NativeTy -> Int -> [Integer] -> Const
      mkVec IT8  len values = B8V  $ V.generate len (fromInteger . (values !!))
      mkVec IT16 len values = B16V $ V.generate len (fromInteger . (values !!))
      mkVec IT32 len values = B32V $ V.generate len (fromInteger . (values !!))
      mkVec IT64 len values = B64V $ V.generate len (fromInteger . (values !!))

intTyName :: IntTy -> String
intTyName ITNative = "Int"
intTyName ITBig = "BigInt"
intTyName (ITFixed sized) = "B" ++ show (nativeTyWidth sized)
intTyName (ITVec ity count) = "B" ++ show (nativeTyWidth ity) ++ "x" ++ show count

iCmp ity op impl irop totality
    = Prim (UN $ "prim__" ++ op ++ intTyName ity)
      (ty (replicate 2 . AType . ATInt $ ity) (AType (ATInt ITNative)))
      2 impl (2, irop ity) totality
iBinOp ity op impl irop totality
    = Prim (UN $ "prim__" ++ op ++ intTyName ity)
      (ty (replicate 2  . AType . ATInt $ ity) (AType . ATInt $ ity))
      2 impl (2, irop ity) totality
iUnOp ity op impl irop totality
    = Prim (UN $ "prim__" ++ op ++ intTyName ity)
      (ty [AType . ATInt $ ity] (AType . ATInt $ ity))
      1 impl (1, irop ity) totality
iCoerce from to op impl irop =
    Prim (UN $ "prim__" ++ op ++ intTyName from ++ "_" ++ intTyName to)
             (ty [AType . ATInt $ from] (AType . ATInt $ to)) 1 (impl from to) (1, irop from to) total

p_believeMe [_,_,x] = Just x
p_believeMe _ = Nothing

fBin op [VConstant (Fl x), VConstant (Fl y)] = Just $ VConstant (Fl (op x y))
fBin _ _ = Nothing

bfBin op [VConstant (Fl x), VConstant (Fl y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bfBin _ _ = Nothing

bcBin op [VConstant (Ch x), VConstant (Ch y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bcBin _ _ = Nothing

bsBin op [VConstant (Str x), VConstant (Str y)] 
    = let i = (if op x y then 1 else 0) in
          Just $ VConstant (I i)
bsBin _ _ = Nothing

sBin op [VConstant (Str x), VConstant (Str y)] = Just $ VConstant (Str (op x y))
sBin _ _ = Nothing

bsrem (ITFixed IT8) [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int8)))
bsrem (ITFixed IT16) [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int16)))
bsrem (ITFixed IT32) [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int32)))
bsrem (ITFixed IT64) [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `rem` fromIntegral y :: Int64)))
bsrem ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `rem` y))
bsrem (ITVec IT8  _) [VConstant (B8V  x), VConstant (B8V  y)]
    = Just . VConstant . B8V  $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `rem` fromIntegral d :: Int8)))  x y
bsrem (ITVec IT16 _) [VConstant (B16V x), VConstant (B16V y)]
    = Just . VConstant . B16V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `rem` fromIntegral d :: Int16))) x y
bsrem (ITVec IT32 _) [VConstant (B32V x), VConstant (B32V y)]
    = Just . VConstant . B32V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `rem` fromIntegral d :: Int64))) x y
bsrem (ITVec IT64 _) [VConstant (B64V x), VConstant (B64V y)]
    = Just . VConstant . B64V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `rem` fromIntegral d :: Int64))) x y
bsrem _ _ = Nothing

bsdiv (ITFixed IT8) [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int8)))
bsdiv (ITFixed IT16) [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int16)))
bsdiv (ITFixed IT32) [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int32)))
bsdiv (ITFixed IT64) [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `div` fromIntegral y :: Int64)))
bsdiv ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `div` y))
bsdiv (ITVec IT8  _) [VConstant (B8V  x), VConstant (B8V  y)]
    = Just . VConstant . B8V  $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `div` fromIntegral d :: Int8)))  x y
bsdiv (ITVec IT16 _) [VConstant (B16V x), VConstant (B16V y)]
    = Just . VConstant . B16V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `div` fromIntegral d :: Int16))) x y
bsdiv (ITVec IT32 _) [VConstant (B32V x), VConstant (B32V y)]
    = Just . VConstant . B32V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `div` fromIntegral d :: Int64))) x y
bsdiv (ITVec IT64 _) [VConstant (B64V x), VConstant (B64V y)]
    = Just . VConstant . B64V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `div` fromIntegral d :: Int64))) x y
bsdiv _ _ = Nothing

bashr (ITFixed IT8) [VConstant (B8 x), VConstant (B8 y)]
    = Just $ VConstant (B8 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int8)))
bashr (ITFixed IT16) [VConstant (B16 x), VConstant (B16 y)]
    = Just $ VConstant (B16 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int16)))
bashr (ITFixed IT32) [VConstant (B32 x), VConstant (B32 y)]
    = Just $ VConstant (B32 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int32)))
bashr (ITFixed IT64) [VConstant (B64 x), VConstant (B64 y)]
    = Just $ VConstant (B64 (fromIntegral (fromIntegral x `shiftR` fromIntegral y :: Int64)))
bashr ITNative [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (x `shiftR` y))
bashr (ITVec IT8  _) [VConstant (B8V  x), VConstant (B8V  y)]
    = Just . VConstant . B8V  $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `shiftR` fromIntegral d :: Int8)))  x y
bashr (ITVec IT16 _) [VConstant (B16V x), VConstant (B16V y)]
    = Just . VConstant . B16V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `shiftR` fromIntegral d :: Int16))) x y
bashr (ITVec IT32 _) [VConstant (B32V x), VConstant (B32V y)]
    = Just . VConstant . B32V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `shiftR` fromIntegral d :: Int64))) x y
bashr (ITVec IT64 _) [VConstant (B64V x), VConstant (B64V y)]
    = Just . VConstant . B64V $
      V.zipWith (\n d -> (fromIntegral (fromIntegral n `shiftR` fromIntegral d :: Int64))) x y
bashr _ _ = Nothing

bUn :: IntTy -> (forall a. Bits a => a -> a) -> [Value] -> Maybe Value
bUn (ITFixed IT8)  op [VConstant (B8  x)] = Just $ VConstant (B8  (op x))
bUn (ITFixed IT16) op [VConstant (B16 x)] = Just $ VConstant (B16 (op x))
bUn (ITFixed IT32) op [VConstant (B32 x)] = Just $ VConstant (B32 (op x))
bUn (ITFixed IT64) op [VConstant (B64 x)] = Just $ VConstant (B64 (op x))
bUn ITBig op [VConstant (BI x)] = Just $ VConstant (BI (op x))
bUn ITNative op [VConstant (I x)] = Just $ VConstant (I (op x))
bUn (ITVec IT8  _) op [VConstant (B8V  x)] = Just . VConstant . B8V  $ V.map op x
bUn (ITVec IT16 _) op [VConstant (B16V x)] = Just . VConstant . B16V $ V.map op x
bUn (ITVec IT32 _) op [VConstant (B32V x)] = Just . VConstant . B32V $ V.map op x
bUn (ITVec IT64 _) op [VConstant (B64V x)] = Just . VConstant . B64V $ V.map op x
bUn _ _ _ = Nothing

bitBin :: IntTy -> (forall a. (Bits a, Integral a) => a -> a -> a) -> [Value] -> Maybe Value
bitBin (ITFixed IT8)  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (B8  (op x y))
bitBin (ITFixed IT16) op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (B16 (op x y))
bitBin (ITFixed IT32) op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (B32 (op x y))
bitBin (ITFixed IT64) op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (B64 (op x y))
bitBin ITBig op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (BI (op x y))
bitBin ITNative op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
bitBin (ITVec IT8  _) op [VConstant (B8V  x), VConstant (B8V  y)]
    = Just . VConstant . B8V  $ V.zipWith op x y
bitBin (ITVec IT16 _) op [VConstant (B16V x), VConstant (B16V y)]
    = Just . VConstant . B16V $ V.zipWith op x y
bitBin (ITVec IT32 _) op [VConstant (B32V x), VConstant (B32V y)]
    = Just . VConstant . B32V $ V.zipWith op x y
bitBin (ITVec IT64 _) op [VConstant (B64V x), VConstant (B64V y)]
    = Just . VConstant . B64V $ V.zipWith op x y
bitBin _ _ _ = Nothing

bCmp :: IntTy -> (forall a. Ord a => a -> a -> Bool) -> [Value] -> Maybe Value
bCmp (ITFixed IT8)  op [VConstant (B8  x), VConstant (B8  y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp (ITFixed IT16) op [VConstant (B16 x), VConstant (B16 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp (ITFixed IT32) op [VConstant (B32 x), VConstant (B32 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp (ITFixed IT64) op [VConstant (B64 x), VConstant (B64 y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp ITBig op [VConstant (BI x), VConstant (BI y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp ITNative op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (if (op x y) then 1 else 0))
bCmp _ _ _ = Nothing

toInt (ITFixed IT8)  x = VConstant (B8 (fromIntegral x))
toInt (ITFixed IT16) x = VConstant (B16 (fromIntegral x))
toInt (ITFixed IT32) x = VConstant (B32 (fromIntegral x))
toInt (ITFixed IT64) x = VConstant (B64 (fromIntegral x))
toInt ITBig x = VConstant (BI (fromIntegral x))
toInt ITNative x = VConstant (I (fromIntegral x))

intToInt (ITFixed IT8) out [VConstant (B8 x)] = Just $ toInt out x
intToInt (ITFixed IT16) out [VConstant (B16 x)] = Just $ toInt out x
intToInt (ITFixed IT32) out [VConstant (B32 x)] = Just $ toInt out x
intToInt (ITFixed IT64) out [VConstant (B64 x)] = Just $ toInt out x
intToInt ITBig out [VConstant (BI x)] = Just $ toInt out x
intToInt ITNative out [VConstant (I x)] = Just $ toInt out x
intToInt _ _ _ = Nothing

zext from ITBig val = intToInt from ITBig val
zext ITBig _ _ = Nothing
zext from to val
    | intTyWidth from < intTyWidth to = intToInt from to val
zext _ _ _ = Nothing

sext (ITFixed IT8)  out [VConstant (B8  x)] = Just $ toInt out (fromIntegral x :: Int8)
sext (ITFixed IT16) out [VConstant (B16 x)] = Just $ toInt out (fromIntegral x :: Int16)
sext (ITFixed IT32) out [VConstant (B32 x)] = Just $ toInt out (fromIntegral x :: Int32)
sext (ITFixed IT64) out [VConstant (B64 x)] = Just $ toInt out (fromIntegral x :: Int64)
sext ITBig _ _ = Nothing
sext from to val = intToInt from to val

trunc ITBig to val = intToInt ITBig to val
trunc _ ITBig _ = Nothing
trunc from to val | intTyWidth from > intTyWidth to = intToInt from to val
trunc _ _ _ = Nothing

getInt :: [Value] -> [Integer]
getInt (VConstant (B8 x) : xs) = toInteger x : getInt xs
getInt (VConstant (B16 x) : xs) = toInteger x : getInt xs
getInt (VConstant (B32 x) : xs) = toInteger x : getInt xs
getInt (VConstant (B64 x) : xs) = toInteger x : getInt xs
getInt (VConstant (I x) : xs) = toInteger x : getInt xs
getInt (VConstant (BI x) : xs) = x : getInt xs
getInt _ = []

intToStr val | [i] <- getInt val = Just $ VConstant (Str (show i))
intToStr _ = Nothing

strToInt ity [VConstant (Str x)] = case reads x of
                                     [(n,"")] -> Just $ toInt ity (n :: Integer)
                                     _ -> Just $ VConstant (I 0)
strToInt _ _ = Nothing

intToFloat val | [i] <- getInt val = Just $ VConstant (Fl (fromIntegral i))
intToFloat _ = Nothing

floatToInt ity [VConstant (Fl x)] = Just $ toInt ity (truncate x :: Integer)
floatToInt _ _ = Nothing

c_intToChar [VConstant (I x)] = Just $ VConstant (Ch (toEnum x))
c_intToChar _ = Nothing
c_charToInt [VConstant (Ch x)] = Just $ VConstant (I (fromEnum x))
c_charToInt _ = Nothing

c_floatToStr [VConstant (Fl x)] = Just $ VConstant (Str (show x))
c_floatToStr _ = Nothing
c_strToFloat [VConstant (Str x)] = case reads x of
                                        [(n,"")] -> Just $ VConstant (Fl n)
                                        _ -> Just $ VConstant (Fl 0)
c_strToFloat _ = Nothing

p_fPrim f [VConstant (Fl x)] = Just $ VConstant (Fl (f x))
p_fPrim f _ = Nothing

p_floatExp = p_fPrim exp
p_floatLog = p_fPrim log
p_floatSin = p_fPrim sin
p_floatCos = p_fPrim cos
p_floatTan = p_fPrim tan
p_floatASin = p_fPrim asin
p_floatACos = p_fPrim acos
p_floatATan = p_fPrim atan
p_floatSqrt = p_fPrim sqrt
p_floatFloor = p_fPrim (fromInteger . floor)
p_floatCeil = p_fPrim (fromInteger . ceiling)

p_strLen [VConstant (Str xs)] = Just $ VConstant (I (length xs))
p_strLen _ = Nothing
p_strHead [VConstant (Str (x:xs))] = Just $ VConstant (Ch x)
p_strHead _ = Nothing
p_strTail [VConstant (Str (x:xs))] = Just $ VConstant (Str xs)
p_strTail _ = Nothing
p_strIndex [VConstant (Str xs), VConstant (I i)] 
   | i < length xs = Just $ VConstant (Ch (xs!!i))
p_strIndex _ = Nothing
p_strCons [VConstant (Ch x), VConstant (Str xs)] = Just $ VConstant (Str (x:xs))
p_strCons _ = Nothing
p_strRev [VConstant (Str xs)] = Just $ VConstant (Str (reverse xs))
p_strRev _ = Nothing

p_cantreduce _ = Nothing

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def sc tot) 
    = do updateContext (addOperator n ty i def)
         setTotality n tot
         i <- getIState
         putIState i { idris_scprims = (n, sc) : idris_scprims i }

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl EAll toplevel) 
                     (map (PData "" defaultSyntax (FC "builtin" 0) False)
                         [inferDecl, unitDecl, falseDecl, pairDecl, eqDecl])
               mapM_ elabPrim primitives

