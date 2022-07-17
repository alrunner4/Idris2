module Control.Monad.STT
import Control.Monad.ST
import Data.IOArray
import Data.IORef

||| The ST monad transformer.
|||
||| `STT s m a` has is an operation on the state thread `s` in `Monad m` with result `a`.
export
data STT: Type -> (Type -> Type) -> Type -> Type where
   MkSTT: IO a -> (a -> m b) -> STT s m b

||| `STTRef s a` is the type of mutable references in state thread `s`.
export
data STTRef: Type -> Type -> Type where
   MkSTTRef: IORef a -> STTRef s a

||| `STTArray s a` is the type of mutable array references in state thread `s`.
export
data STTArray: Type -> Type -> Type where
   MkSTTArray: IOArray a -> STTArray s a

||| `runSTT op` creates a state thread and uses it to evaluate the mutable computation `op` which
||| may have actions in `Monad m` in addition to `MonadST`.
export runSTT: (forall s. STT s m a) -> m a
runSTT p = let MkSTT st act = p {s = ()} in act (unsafePerformIO st)

public export
interface Monad m => MonadST (m: Type -> Type) where
   constructor MkMonadST
   VarRef: Type -> Type -> Type
   ArrayRef: Type -> Type -> Type
   newSTTRef: a -> m (VarRef s a)
   readSTTRef: VarRef s a -> m a
   writeSTTRef: VarRef s a -> a -> m ()
   newSTTArray: Int -> m (ArrayRef s a)
   readSTTArray: ArrayRef s a -> Int -> m (Maybe a)
   writeSTTArray: ArrayRef s a -> Int -> a -> m Bool

export
Functor m => Functor (STT s m) where
   map f (MkSTT st m_a) = MkSTT st (\x => map f (m_a x))

export
Applicative m => Applicative (STT s m) where
   pure x = MkSTT (pure ()) (const$ pure x)
   MkSTT st1 f <*> MkSTT st2 x = MkSTT (pure ()) $const$
      f (unsafePerformIO st1) <*> x (unsafePerformIO st2)

export
{0 s: _} -> Monad m => Monad (STT s m) where
   MkSTT stt1 act >>= f = MkSTT (pure ()) $const$ do
      r1 <- act (unsafePerformIO stt1)
      let MkSTT stt2 act2 = f r1
      act2 (unsafePerformIO stt2)

export
{m: Type -> Type} -> {s: Type} -> Monad m => MonadST (STT s m) where
   VarRef = STTRef
   ArrayRef = STTArray
   newSTTRef = \x => MkSTT (newIORef x) (pure . MkSTTRef)
   readSTTRef = \(MkSTTRef r) => MkSTT (readIORef r) pure
   writeSTTRef = \(MkSTTRef r), x => MkSTT (writeIORef r x) pure
   newSTTArray = \size => MkSTT (newArray size) (pure . MkSTTArray)
   readSTTArray = \(MkSTTArray r), i => MkSTT (readArray r i) pure
   writeSTTArray = \(MkSTTArray r), i, x => MkSTT (writeArray r i x) pure

