{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Categorical.Bifunctor (
    lmap,
    rmap,
    bimap,
    (***),

    Associative (..),

    Braided (..),

    Monoidal (..),

    MonoidalObject (..),

    Cartesian (..),
    (|||),

    MonoidalFunctor (..),
) where

import Control.Categorical.Functor
import Control.Category.Dual
import Data.Either
import Data.Proxy
import Data.Void

lmap :: Functor r (NT t) f => r a b -> t (f a c) (f b c)
lmap = nt . map

rmap :: Functor s t (f a) => s b c -> t (f a b) (f a c)
rmap = map

infixr 3 ***
bimap, (***) :: (Functor r (NT t) f, ∀ a . Functor s t (f a)) => r a₁ b₁ -> s a₂ b₂ -> t (f a₁ a₂) (f b₁ b₂)
bimap f g = lmap f . map g
(***) = bimap

class (Functor s (NT s) p, ∀ a . Endofunctor s (p a)) => Associative s p where
    assoc :: s (p (p a b) c) (p a (p b c))
    disassoc :: s (p a (p b c)) (p (p a b) c)

instance Associative (->) (,) where
    assoc ((a, b), c) = (a, (b, c))
    disassoc (a, (b, c)) = ((a, b), c)

instance Associative (->) Either where
    assoc = \ case
        Left (Left a) -> Left a
        Left (Right b) -> Right (Left b)
        Right c -> Right (Right c)
    disassoc = \ case
        Left a -> Left (Left a)
        Right (Left b) -> Left (Right b)
        Right (Right c) -> Right c

instance Associative s p => Associative (Dual s) p where
    assoc = Dual disassoc
    disassoc = Dual assoc

class Associative s p => Braided s p where
    braid :: s (p a b) (p b a)

instance Braided (->) (,) where
    braid (a, b) = (b, a)

instance Braided (->) Either where
    braid = either Right Left

instance Braided s p => Braided (Dual s) p where
    braid = Dual braid

class Braided s p => Symmetric s p
instance Symmetric (->) (,)
instance Symmetric (->) Either
instance Symmetric s p => Symmetric (Dual s) p

class Associative s p => Monoidal s p where
    type Id s p :: k
    idL :: s (p (Id s p) a) a
    idR :: s (p a (Id s p)) a
    coidL :: s a (p (Id s p) a)
    coidR :: s a (p a (Id s p))

instance Monoidal (->) (,) where
    type Id (->) (,) = ()
    idL ((), a) = a
    idR (a, ()) = a
    coidL a = ((), a)
    coidR a = (a, ())

instance Monoidal (->) Either where
    type Id (->) Either = Void
    idL = either (\ case) id
    idR = either id (\ case)
    coidL = Right
    coidR = Left

instance Monoidal s p => Monoidal (Dual s) p where
    type Id (Dual s) p = Id s p
    idL = Dual coidL
    idR = Dual coidR
    coidL = Dual idL
    coidR = Dual idR

class Monoidal s p => MonoidalObject s p a where
    η :: Proxy p -> s (Id s p) a
    μ :: s (p a a) a

infixr 3 &&&
class (Symmetric s (Product s), Monoidal s (Product s)) => Cartesian s where
    {-# MINIMAL fst, snd, (diag | (&&&)) #-}
    type Product s :: k -> k -> k
    fst :: s (Product s a b) a
    snd :: s (Product s a b) b
    diag :: s a (Product s a a)
    (&&&) :: ∀ a b c . s a b -> s a c -> s a (Product s b c)

    diag = id &&& id
    f &&& g = case lemma3 :: _ (Endofunctor s (Product s a)) of Sub lemma3' -> lmap f . lemma3' (rmap g) . diag

data Sub a b = Sub (∀ x . (b => x) -> (a => x))

instance Category Sub where
    id = Sub (\ x -> x)
    Sub f . Sub g = Sub (\ x -> g (f x))

lemma1 :: Sub (Monoidal s p) (Functor s s (p a))
lemma1 = Sub (\ x -> x)

lemma2 :: Sub (Cartesian s) (Monoidal s (Product s))
lemma2 = Sub (\ x -> x)

lemma3 :: Sub (Cartesian s) (Functor s s (Product s a))
lemma3 = lemma1 . lemma2

instance Cartesian (->) where
    type Product (->) = (,)
    fst (a, _) = a
    snd (_, b) = b
    (f &&& g) a = (f a, g a)

instance Cartesian (Dual (->)) where
    type Product (Dual (->)) = Either
    fst = Dual Left
    snd = Dual Right
    Dual f &&& Dual g = Dual (either f g)

infixr 2 |||
(|||) :: Cartesian (Dual s) => s a c -> s b c -> s (Product (Dual s) a b) c
f ||| g = dual (Dual f &&& Dual g)

class (Monoidal s p, Monoidal t q, Functor s t f) => MonoidalFunctor s t p q f where
    zip :: Proxy s -> t (q (f a) (f b)) (f (p a b))
    pure :: Proxy s -> Proxy p -> Proxy q -> t (Id t q) (f (Id s p))
