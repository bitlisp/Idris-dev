import Prelude.List
import Prelude.Bits

%access public

abstract data IO a = prim__IO a

abstract
io_bind : IO a -> (a -> IO b) -> IO b
io_bind (prim__IO v) k = k v

unsafePerformIO : IO a -> a
-- compiled as primitive

abstract
io_return : a -> IO a
io_return x = prim__IO x

-- This may seem pointless, but we can use it to force an
-- evaluation of main that Epic wouldn't otherwise do...

run__IO : IO () -> IO ()
run__IO v = io_bind v (\v' => io_return v')

data FTy = FInt | FFloat | FChar | FString | FPtr | FAny Type | FUnit
         | FBits8 | FBits16 | FBits32 | FBits64

interpFTy : FTy -> Type
interpFTy FInt     = Int
interpFTy FFloat   = Float
interpFTy FChar    = Char
interpFTy FString  = String
interpFTy FPtr     = Ptr
interpFTy (FAny t) = t
interpFTy FUnit    = ()
interpFTy FBits8   = Bits8
interpFTy FBits16  = Bits16
interpFTy FBits32  = Bits32
interpFTy FBits64  = Bits64

interpWrappedFTy : FTy -> Type
interpWrappedFTy FBits8  = Bits 8
interpWrappedFTy FBits16 = Bits 16
interpWrappedFTy FBits32 = Bits 32
interpWrappedFTy FBits64 = Bits 64
interpWrappedFTy x = interpFTy x

WrappedFTy : (ts : List FTy) -> (t : FTy) -> Type
WrappedFTy Nil     rt = IO (interpWrappedFTy rt)
WrappedFTy (t::ts) rt = interpWrappedFTy t -> WrappedFTy ts rt

ForeignTy : (xs:List FTy) -> (t:FTy) -> Type
ForeignTy Nil     rt = IO (interpFTy rt)
ForeignTy (t::ts) rt = interpFTy t -> ForeignTy ts rt

wrapFFun : (ts : List FTy) -> (t : FTy) -> ForeignTy ts t -> WrappedFTy ts t
wrapFFun Nil FBits8   f = f `io_bind` (io_return . MkBits)
wrapFFun Nil FBits16  f = f `io_bind` (io_return . MkBits)
wrapFFun Nil FBits32  f = f `io_bind` (io_return . MkBits)
wrapFFun Nil FBits64  f = f `io_bind` (io_return . MkBits)
wrapFFun Nil FInt     f = f -- Is there any way to avoid enumerating these explicitly?
wrapFFun Nil FFloat   f = f
wrapFFun Nil FChar    f = f
wrapFFun Nil FString  f = f
wrapFFun Nil FPtr     f = f
wrapFFun Nil (FAny _) f = f
wrapFFun Nil FUnit    f = f
-- FIXME: Absurdly slow typechecking
wrapFFun (FBits8 ::ts) t f = (\(MkBits b) => wrapFFun ts t (f b))
wrapFFun (FBits16::ts) t f = (\(MkBits b) => wrapFFun ts t (f b))
wrapFFun (FBits32::ts) t f = (\(MkBits b) => wrapFFun ts t (f b))
wrapFFun (FBits64::ts) t f = (\(MkBits b) => wrapFFun ts t (f b))
wrapFFun (FInt::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FFloat::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FChar::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FString::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FPtr::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FAny _::ts) t f = (\x => wrapFFun ts t (f x))
wrapFFun (FUnit::ts) t f = (\x => wrapFFun ts t (f x))


data Foreign : Type -> Type where
    FFun : String -> (xs:List FTy) -> (t:FTy) -> 
           Foreign (ForeignTy xs t)

mkForeign : Foreign x -> x
mkLazyForeign : Foreign x -> x
-- mkForeign and mkLazyForeign compiled as primitives

fork : |(thread:IO ()) -> IO Ptr
fork x = io_return prim__vm -- compiled specially
