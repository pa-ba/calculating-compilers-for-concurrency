{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Definition of the semantics of CTrees in terms of labelled
-- transition systems.
------------------------------------------------------------------------


module CTree.Transitions where

open import CTree.Definitions
open import Data.Nat
open import Data.Nat.Induction
open import Relation.Nullary
open import Data.Product
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

-- The LTS has transitions that are either labelled by a τ (silent
-- transition) or an action ε e (effect e), ι r (input r), ρ v (return
-- v).

data action (E : Set → Set) (A : Set) : Set₁ where
  ε : ∀ {B} → E B → action E A
  ι : ∀ {B : Set} → B → action E A
  ρ :  A → action E A

data label (E : Set → Set) (A : Set) : Set₁ where
  ⟨_⟩ : action E A → label E A
  τ :  label E A


-- retFree l l' indicates that l and l' are equal and not of the form
-- ⟨ρ _⟩.

data retFree {E : Set → Set} {A B : Set} : label E A → label E B → Set where
  retFreeε : ∀ {B} {e : E B} → retFree ⟨ ε e ⟩ ⟨ ε e ⟩
  retFreeι : ∀ {B} {r : B} → retFree ⟨ ι r ⟩ ⟨ ι r ⟩
  retFreeτ : retFree τ τ

retFreeAction : {E : Set → Set} {A B : Set} { a : action E A} {l : label E B}
  → retFree ⟨ a ⟩ l -> ∃[ a' ] l ≡ ⟨ a' ⟩
retFreeAction retFreeε = _ , refl
retFreeAction retFreeι = _ , refl

retFree-trans : ∀ {E A B C} {l : label E A} {l' : label E B} {l'' : label E C}
  → retFree l l' → retFree l' l'' → retFree l l''
retFree-trans retFreeε retFreeε = retFreeε
retFree-trans retFreeι retFreeι = retFreeι
retFree-trans retFreeτ retFreeτ = retFreeτ

retFree-refl : ∀ {E A B} {l : label E A} {l' : label E B} 
  → retFree l l' → retFree l' l'
retFree-refl retFreeε = retFreeε
retFree-refl retFreeι = retFreeι
retFree-refl retFreeτ = retFreeτ


retFree-sym : ∀ {E A B} {l : label E A} {l' : label E B} 
  → retFree l l' → retFree l' l
retFree-sym retFreeε = retFreeε
retFree-sym retFreeι = retFreeι
retFree-sym retFreeτ = retFreeτ



retFreeCoerce : {E : Set → Set} {A B C : Set} {l : label E A} {l' : label E B} → retFree l l' → label E C
retFreeCoerce {l = ⟨ ε v ⟩} retFreeε =  ⟨ ε v ⟩
retFreeCoerce {l = ⟨ ι v ⟩}retFreeι = ⟨ ι v ⟩
retFreeCoerce retFreeτ = τ

coerce-retFree : {E : Set → Set} {A B C : Set} {l : label E A} {l' : label E B}
  → (rf : retFree l l') → retFree l (retFreeCoerce {C = C} rf)
coerce-retFree retFreeε = retFreeε
coerce-retFree retFreeι = retFreeι
coerce-retFree retFreeτ = retFreeτ

coerce-retFree' : {E : Set → Set} {A B C : Set} {l : label E A} {l' : label E B}
  → (rf : retFree l l') → retFree (retFreeCoerce {C = C} rf) l'
coerce-retFree' retFreeε = retFreeε
coerce-retFree' retFreeι = retFreeι
coerce-retFree' retFreeτ = retFreeτ


lmap : ∀ {E A B} (f : A → B) → label E A → label E B
lmap f ⟨ ε x ⟩ = ⟨ ε x ⟩
lmap f ⟨ ι x ⟩ = ⟨ ι x ⟩
lmap f ⟨ ρ x ⟩ = ⟨ ρ (f x )⟩
lmap f τ = τ


retFree-lmap : ∀ {E A B l} {l' : label E B} (f : A → B) → retFree l l' → lmap f l ≡ l'
retFree-lmap f retFreeε = refl
retFree-lmap f retFreeι = refl
retFree-lmap f retFreeτ = refl


-- Generalised choice tree: It is either a choice tree or a choice
-- tree that is waiting for some input
data CTree' E A : Set₁ where
  _↑ : (p : CTree E A ∞) → CTree' E A
  wait : ∀ (B : Set) → (c : B → CTree E A ∞) → CTree' E A

-- The labelled transition relation on generalised choice trees.

infix 3 _[_]⇒_
data _[_]⇒_  {E A} : CTree' E A → label E A → CTree' E A → Set₁ where
  ⇒-eff : ∀ {B} (e : E B) c → eff e c ↑ [ ⟨ ε e ⟩ ]⇒ wait B c
  ⇒-inp : ∀ {B} (r : B) c → wait B c [ ⟨ ι r ⟩ ]⇒ c r ↑
  ⇒-now : ∀ v → now v ↑ [ ⟨ ρ v ⟩ ]⇒ ∅ ↑
  ⇒-⊕-l : ∀ {l p1 p2 p} → p1 ↑ [ l ]⇒ p → (p1 ⊕ p2) ↑ [ l ]⇒ p 
  ⇒-⊕-r : ∀ {l p1 p2 p} → p2 ↑ [ l ]⇒ p → (p1 ⊕ p2) ↑ [ l ]⇒ p
  ⇒-later : ∀ {p} → later p ↑ [ τ ]⇒ force p ↑

-- The labelled transition relation restricted to only
-- (non-generalised) choice trees.

infix 3 _[_]=>_
_[_]=>_  : ∀ {E A} → CTree E A ∞ → label E A → CTree E A ∞ → Set₁
p [ l ]=> q = p ↑ [ l ]⇒ q ↑

∅-no-step : ∀ {E A lv p} {B : Set lv} {l : label E A} → ∅ ↑ [ l ]⇒ p → B
∅-no-step ()


⇒-ι-↑ : ∀ {E A B q} {r : B} {p : CTree E A ∞} → ¬ ((p ↑) [ ⟨ ι r ⟩ ]⇒ q)
⇒-ι-↑ (⇒-⊕-l tr) = ⇒-ι-↑ tr
⇒-ι-↑ (⇒-⊕-r tr) = ⇒-ι-↑ tr

⇒-τ-↑ : ∀ {E A q} {p : CTree' E A} →  p [ τ ]⇒ q → ∃[ q' ] q ≡ q' ↑
⇒-τ-↑ (⇒-⊕-l tr) with _ , refl ← ⇒-τ-↑ tr = _ , refl
⇒-τ-↑ (⇒-⊕-r tr) with _ , refl ← ⇒-τ-↑ tr = _ , refl
⇒-τ-↑ ⇒-later = -, refl

⇒-ε-wait : ∀ {E A B q} {e : E B} {p : CTree' E A} →  p [ ⟨ ε e ⟩ ]⇒ q → ∃[ q' ] q ≡ wait B q'
⇒-ε-wait (⇒-eff _ c) = -, refl
⇒-ε-wait (⇒-⊕-l tr) with _ , refl ← ⇒-ε-wait tr = -, refl
⇒-ε-wait (⇒-⊕-r tr) with _ , refl ← ⇒-ε-wait tr = -, refl

⇒-ρ-∅ : ∀ {E A} {p : CTree' E A} {q v} → p [ ⟨ ρ v ⟩ ]⇒ q → q ≡ ∅ ↑
⇒-ρ-∅ (⇒-now _) = refl
⇒-ρ-∅ (⇒-⊕-l tr) = ⇒-ρ-∅ tr
⇒-ρ-∅ (⇒-⊕-r tr) = ⇒-ρ-∅ tr

-- The labelled transition relation is well-founded.

infix 3 _⇐_

_⇐_ : ∀ {E A} → CTree' E A → CTree' E A → Set₁
p ⇐ q = ∃[ a ] q [ ⟨ a ⟩ ]⇒ p

mutual
  ⇐-wf : ∀ {E A} →  WellFounded (_⇐_ {E} {A})
  ⇐-wf (x ↑) = ⇐-wf↑ x
  ⇐-wf (wait B x) = ⇐-wf-wait x

  private
    ⇐-wf↑ : ∀ {E A} →  ∀ p → Acc (_⇐_ {E} {A}) (p ↑)
    ⇐-wf↑ p = acc  down
      where ⇐-wf-∅ : ∀ {E A} →  (Acc (_⇐_ {E} {A})) (∅ ↑)
            ⇐-wf-∅ =  acc λ _ ()

            down : ∀ q → q ⇐ p ↑ → (Acc _⇐_) q
            down _ (_ , ⇒-eff e c) = ⇐-wf-wait c
            down _ (_ , ⇒-now v) = ⇐-wf-∅
            down q (a , ⇒-⊕-l trans) with ⇐-wf↑ _
            ... | acc rs =  rs q ( _ , trans)
            down q (a , ⇒-⊕-r trans) with ⇐-wf↑ _
            ... | acc rs =  rs q ( _ , trans)

    ⇐-wf-wait : ∀ {E A B} →  ∀ p → Acc (_⇐_ {E} {A}) (wait B p )
    ⇐-wf-wait c = acc (λ { _ (_ , ⇒-inp r .c) → ⇐-wf↑ (c r)})


-- We are going to use well-founded recursion on a couple of
-- well-founded relations based on ⇐

<×⇐-wf : ∀ {E A} →  WellFounded (×-Lex _≡_ _<_ (_⇐_ {E} {A}))
<×⇐-wf = ×-wellFounded <-wellFounded ⇐-wf

<×⇐×⇐-wf : ∀ {E E' A A'} →  WellFounded (×-Lex _≡_ _<_ (×-Lex _≡_ (_⇐_ {E} {A}) (_⇐_ {E'} {A'})))
<×⇐×⇐-wf = ×-wellFounded <-wellFounded (×-wellFounded ⇐-wf ⇐-wf)

-- Transitive closure of ⇐
_⇐⁺_ : ∀ {E A} → CTree' E A → CTree' E A → Set₁
_⇐⁺_ = TransClosure _⇐_

⇐⁺-wf : ∀ {E A} →  WellFounded (_⇐⁺_ {E} {A})
⇐⁺-wf = wellFounded _⇐_ ⇐-wf

<×⇐⁺-wf : ∀ {E A} →  WellFounded (×-Lex _≡_ _<_ (_⇐⁺_ {E} {A}))
<×⇐⁺-wf = ×-wellFounded <-wellFounded ⇐⁺-wf

<×⇐⁺×⇐⁺-wf : ∀ {E E' A A'} →  WellFounded (×-Lex _≡_ _<_ (×-Lex _≡_ (_⇐⁺_ {E} {A}) (_⇐⁺_ {E'} {A'})))
<×⇐⁺×⇐⁺-wf = ×-wellFounded <-wellFounded (×-wellFounded ⇐⁺-wf ⇐⁺-wf)

<×⇐⁺×⇐⁺×⇐⁺-wf : ∀ {E E' E'' A A' A''} →  WellFounded (×-Lex _≡_ _<_ (×-Lex _≡_ (_⇐⁺_ {E} {A})
  (×-Lex _≡_ (_⇐⁺_ {E'} {A'}) (_⇐⁺_ {E''} {A''}))))
<×⇐⁺×⇐⁺×⇐⁺-wf = ×-wellFounded <-wellFounded (×-wellFounded ⇐⁺-wf (×-wellFounded ⇐⁺-wf ⇐⁺-wf))
