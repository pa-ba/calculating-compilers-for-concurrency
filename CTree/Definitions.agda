{-# OPTIONS --copatterns --sized-types #-}

module CTree.Definitions where

open import Size public
open import Data.Nat
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Data.Fin
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

infixl 7 _⊕_


-- Definition of choice trees.

mutual
  data CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    now   : (v : A) → CTree E A i
    later : (p : ∞CTree E A i) → CTree E A i
    _⊕_   : (p q : CTree E A i) → CTree E A i
    ∅     : CTree E A i
    eff   : ∀ {B} → (e : E B) → (c : B → CTree E A i) → CTree E A i

  record ∞CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CTree E A j

open ∞CTree public

infixl 5 _>>=_
infixl 5 _>>_

-- Monadic bind operator.

mutual
  _>>=_ : ∀ {i A B E} → CTree E A i → (A → CTree E B i) → CTree E B i
  now   x >>= f = f x
  (later x) >>= f = later (x ∞>>= f)
  p ⊕ q >>= f = (p >>= f) ⊕ (q >>= f)
  ∅ >>= f = ∅
  eff e c >>= f = eff e (λ x → c x >>= f)

  _∞>>=_ :  ∀ {i A B E} → ∞CTree E A i → (A → CTree E B i) → ∞CTree E B i
  force (x ∞>>= f) = force x >>= f

_>>_ : ∀ {i A B E} → CTree E A i → (CTree E B i) → CTree E B i
p >> q = p >>= λ _ → q

-- Monadic return operator

return : ∀ {i E A} → A → CTree E A i
return = now

∞ret : ∀ {A E i} → (v : A) → ∞CTree E A i
force (∞ret v) = return v

-- Functorial map operator derived from >>=

map : ∀ {i A B E} → (A → B) → CTree E A i → CTree E B i
map f p = p >>= (λ x → return (f x))

∞map : ∀ {i A B E} → (A → B) → ∞CTree E A i → ∞CTree E B i
∞map f p = p ∞>>= (λ x → return (f x))

-- The purely diverging choice tree.

mutual
  never : ∀ {E A i} -> CTree E A i
  never = later ∞never

  ∞never : ∀ {E A i} -> ∞CTree E A i
  force ∞never = never

--------------------
-- interpretation --
--------------------

-- We have various combinators to interpret (or handle) the effects of
-- a choice tree. The most general of that is `interpSt`, which is the
-- stateful interpretation of effects. The effect handler takes the
-- current state (of type S) as an argument and produces new states in
-- each of the leaves of the choice tree it produces.

mutual
  interpSt : ∀ {i E F A S} → S → (∀ {B} → S → E B → CTree F (B × S) ∞) → CTree E A i → CTree F A i
  interpSt s f (now v) = now v
  interpSt s f (later p) = later (∞interpSt s f p)
  interpSt s f (p1 ⊕ p2) = interpSt s f p1 ⊕ interpSt s f p2
  interpSt s f ∅ = ∅
  interpSt s f (eff e c) = f s e >>= (λ (x , s') → interpSt s' f (c x))

  ∞interpSt : ∀ {i E F A S} → S → (∀ {B} → S → E B → CTree F (B × S) ∞) → ∞CTree E A i → ∞CTree F A i
  force (∞interpSt s f p) = interpSt s f (force p)

-- This is the standard effect interpretation function (without
-- state).

interp : ∀ {i E F A} → (∀ {B} → E B → CTree F B ∞) → CTree E A i → CTree F A i
interp f = interpSt tt (λ s x → map (λ y → y , tt) (f x))
