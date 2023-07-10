{-# OPTIONS --copatterns --sized-types #-}

module CTree.Parallel where


open import CTree.Definitions
open import CTree.IndexedBisimilarity.BasicProperties
open import Data.Nat
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Data.Fin
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

--------------------------
-- parallel composition --
--------------------------


-- Elements of this types are used to handle simultaneous
-- effects. Given two simultaneous effects `e1` and `e2` the handler
-- returns `nothing` to indicate that `e1` and `e2` are not allowed to
-- occur simultaneously, and `just (r1, r2)` indicates that they are
-- allowed and are handled by returning `r1` and `r2` as result of
-- `e1` and `e2`, respectively.

record Concurrent (E : Set → Set) : Set₁ where
  field
    _⇄_ : ∀ {A B} → E A → E B → CTree E (A × B) ∞
    ⇄-sym : ∀ {A B} (e : E A) (e' : E B) {v w} → e ⇄ e' [ τ ]=> return (v , w) → e' ⇄ e [ τ ]=> return (w , v)
    ⇄-step : ∀ {A B} (e : E A) (e' : E B) {l} {p} → (e ⇄ e') ↑ [ l ]⇒ p → l ≡ τ × ∃[ v ] p ≡ return v ↑


open Concurrent {{...}} public

defaultPar : ∀ {E : Set → Set} → Concurrent E
defaultPar = record { _⇄_ = λ _ _ → ∅; ⇄-sym = λ { _ _ ()} ; ⇄-step = λ { _ _ ()}}


⇄-τ : ∀ {E A B l} {{_ : Concurrent E}} (e1 : E A) (e2 : E B) {p : CTree' E (A × B)} → (e1 ⇄ e2) ↑ [ l ]⇒ p → l ≡ τ
⇄-τ e1 e2 tr = proj₁ (⇄-step e1 e2 tr)

⇄-return : ∀ {E A B l} {{_ : Concurrent E}} (e1 : E A) (e2 : E B) {p : CTree' E (A × B)} → (e1 ⇄ e2) ↑ [ l ]⇒ p → ∃[ v ] p ≡ return v ↑
⇄-return e1 e2 tr = proj₂ (⇄-step e1 e2 tr)



infixl 7 _∥_

infixl 7 _∥⃗_


mutual
  -- `par h p q` is the parallel composition of `p` and `q` where
  -- simultaneous effects of `p` and `q` are handled by `h`.
  _∥_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → CTree E B i → CTree E (A × B) i
  p ∥ q =  p ⦉ q ⊕ p ⦊ q ⊕ p ⋈ q


  -- Helper functions for `par`.

  _⦉_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → CTree E B i → CTree E (A × B) i
  now v ⦉ q = ∅
  later p ⦉ q = later (p ∞∥ q)
  (p1 ⊕ p2) ⦉ q = p1 ⦉ q ⊕ p2 ⦉ q
  ∅ ⦉ q = ∅
  eff e c ⦉ q = eff e λ r → c r ∥ q
  
  _⦊_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → CTree E B i → CTree E (A × B) i
  p ⦊ now v = ∅
  p ⦊ later q = later (p ∥∞ q)
  p ⦊ (q1 ⊕ q2) = p ⦊ q1 ⊕ p ⦊ q2
  p ⦊ ∅ = ∅
  p ⦊ eff e c = eff e λ r → p ∥ c r
  
 
  _⋈_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → CTree E B i → CTree E (A × B) i
  (p1 ⊕ p2) ⋈ q = p1 ⋈ q ⊕ p2 ⋈ q
  p ⋈ (q1 ⊕ q2) = p ⋈ q1 ⊕ p ⋈ q2
  now v ⋈ now w = now (v , w)
  eff e1 c1 ⋈ eff e2 c2 = e1 ⇄ e2 >>= λ (r1 , r2) → c1 r1 ∥ c2 r2
  _ ⋈ _ = ∅


  _∥∞_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → ∞CTree E B i → ∞CTree E (A × B) i
  force (p ∥∞ q) = p ∥ force q
  
  _∞∥_ : ∀ {i A B E} {{_ : Concurrent E}} → ∞CTree E A i → CTree E B i → ∞CTree E (A × B) i
  force (p ∞∥ q) = force p ∥ q


-- This is a variant of ∥ that only returns the result of the
-- right-hand side parallel computation.


  _∥⃗_ : ∀ {i A B E} {{_ : Concurrent E}} → CTree E A i → CTree E B i → CTree E B i
  p ∥⃗ q = map proj₂ (p ∥ q)

