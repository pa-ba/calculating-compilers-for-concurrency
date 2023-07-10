{-# OPTIONS --sized-types #-}

------------------------------------------------------
-- Definition of step-indexed (strong) bisimilarity
------------------------------------------------------


module CTree.IndexedBisimilarity.Definitions where

open import CTree.Definitions public
open import CTree.Transitions public
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

lsuc : ∀ {E A} → label E A → ℕ → ℕ
lsuc ⟨ x ⟩ i = suc i
lsuc τ i = i

infix 3 _~̂[_]_

data _~̂[_]_  {E A} : CTree' E A → ℕ → CTree' E A → Set₁ where
  ~izero : ∀ {p q} →  p ~̂[ 0 ] q
  ~istep : ∀ {p q i} →
    (left : ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')) → 
    (right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂[ lsuc l i ] q')) →
    p ~̂[ suc i ] q

infix 3 _~[_]_

_~[_]_ : ∀ {E A} → CTree E A ∞ → ℕ → CTree E A ∞ → Set₁
p ~[ i ] q = p ↑ ~̂[ i ] q ↑


~ileft : ∀ {E A i} {p q : CTree' E A} → p ~̂[ suc i ] q → ∀ {l p'}
  → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')
~ileft (~istep left right) =  left

~iright : ∀ {E A i} {p q : CTree' E A} → p ~̂[ suc i ] q → ∀ {l q'}
  → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂[ lsuc l i ] q')
~iright (~istep left right) = right


lsuc-mono : ∀ {E A j n} (l : label E A) → j ≤ n → lsuc l j ≤ lsuc l n
lsuc-mono ⟨ x ⟩ le = s≤s le
lsuc-mono τ le = le

lsuc-lmap : ∀ {E A B i} {f : A → B} (l : label E A) → lsuc (lmap f l) i ≡ lsuc l i
lsuc-lmap ⟨ ε x ⟩ = refl
lsuc-lmap ⟨ ι x ⟩ = refl
lsuc-lmap ⟨ ρ x ⟩ = refl
lsuc-lmap τ = refl

lsuc≤suc :  ∀ {E A} (l : label E A) i → lsuc l i ≤ suc i
lsuc≤suc ⟨ x ⟩ i = ≤-refl
lsuc≤suc τ i = n≤1+n i

lsuc-retFree : ∀ {E A B} {l : label E A} {l' : label E B} → retFree l l' → (i : ℕ) → lsuc l i ≡ lsuc l' i
lsuc-retFree retFreeε _ = refl
lsuc-retFree retFreeι _ = refl
lsuc-retFree retFreeτ _ = refl
