module Exception where

import Control.Monad (ap,liftM)

data Exception a b = Exn a | NoExn b deriving Show

instance Functor (Exception a) where
    fmap = liftM

instance Applicative (Exception a) where
    pure x = NoExn x
    (<*>) = ap

instance Monad (Exception a) where
    (>>=) (Exn d) f = (Exn d)
    (>>=) (NoExn a) f = f a

handle :: Exception a b -> (a -> Exception a b) -> Exception a b
handle x f = case x of
               Exn c -> f c
               NoExn a -> NoExn a

throw :: a -> Exception a b
throw x = Exn x

returnval (NoExn a) = a
