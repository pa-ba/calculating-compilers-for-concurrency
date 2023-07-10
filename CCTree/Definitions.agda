{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CCTree.Definitions where
open import Data.Product hiding (map)
open import Size public
open import Data.Unit
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Data.Bool
open import CTree using (CTree; ∞CTree; force; CTree' ; Concurrent ; _~̂[_]_; defaultPar; _⇄_ ; ⇄-sym ; ⇄-step) public
open import CTree.Transitions renaming (_[_]=>_ to _[_]=>'_ ; _[_]⇒_ to _[_]⇒'_) public
import CTree as CT
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Relation.Nullary

infixl 7 _∥⃗_
infixl 7 _⊕_
infixl 5 _>>=_
infixl 5 _>>_


mutual
  private data CCTree' (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    now'   : (v : A) → CCTree' E A i
    later' : (p : ∞CCTree E A i) → CCTree' E A i
    _⊕'_   : (p q : CCTree' E A i) → CCTree' E A i
    ∅'     : CCTree' E A i
    eff'   : ∀ {B} → (e : E B) → (c : B → CCTree' E A i) → CCTree' E A i
    _>>='_ : ∀ {B} → CCTree' E B i → (B → CCTree' E A i) → CCTree' E A i
    _∥⃗'_ : ∀ {B} → CCTree' E B i → CCTree' E A i → CCTree' E A i
    interpSt' : ∀ {F S}  {{_ : Concurrent F}} → S → (∀ {B} → S → F B → CTree E (B × S) ∞) → CCTree' F A i → CCTree' E A i

  record ∞CCTree E (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CCTree' E A j

open ∞CCTree public
CCTree : (Set → Set) → Set → Size → Set₁
CCTree = CCTree'


-- Monadic bind operator.

mutual 
  ⟦_⟧ : ∀ {i A E} {{_ : Concurrent E}} → CCTree E A i → ∀ {R} → (A → CTree E R i) → CTree E R i
  ⟦ now' v ⟧ k = k v
  ⟦ later' p ⟧ k = CT.later (⟦ p ⟧∞ k)
  ⟦ p ⊕' q ⟧ k = ⟦ p ⟧ k CT.⊕ ⟦ q ⟧ k
  ⟦ ∅' ⟧ k = CT.∅
  ⟦ eff' e c ⟧ k = CT.eff e (λ r → ⟦ c r ⟧ k)
  ⟦ p >>=' f ⟧ k = ⟦ p ⟧ (λ r → ⟦ f r ⟧ k)
  ⟦ p ∥⃗' q ⟧ k =  ⟦ p ⟧ CT.now CT.∥⃗ ⟦ q ⟧ k
  ⟦ interpSt' s f p ⟧ k = CT.interpSt s f (⟦ p ⟧ CT.now) CT.>>= k
  
  ⟦_⟧∞ : ∀ {i A E} {{_ : Concurrent E}} → ∞CCTree E A i → ∀ {R} → (A → CTree E R i) → ∞CTree E R i
  force (⟦ p ⟧∞ k) = ⟦ force p ⟧ k



now   : ∀ {E A i} (v : A) → CCTree E A i
now = now'

later : ∀ {E A i}  (p : ∞CCTree E A i) → CCTree E A i
later = later'

_⊕_   : ∀ {E A i} (p q : CCTree E A i) → CCTree E A i
_⊕_ = _⊕'_

∅ : ∀ {E A i} → CCTree E A i
∅ = ∅'

eff   : ∀ {E A i} {B} → (e : E B) → (c : B → CCTree E A i) → CCTree E A i
eff = eff'

_>>=_ : ∀ {E A i}{B} → CCTree E B i → (B → CCTree E A i) → CCTree E A i
_>>=_ = _>>='_

_∥⃗_ : ∀ {E A i} {B} → {{_ : Concurrent E}} → CCTree E B i → CCTree E A i → CCTree E A i
_∥⃗_ = _∥⃗'_

interpSt : ∀ {E A i F S} {{_ : Concurrent E}} {{_ : Concurrent F}} → S → (∀ {B} → S → F B → CCTree E (B × S) ∞) → CCTree F A i → CCTree E A i
interpSt s f = interpSt' s (λ st e → ⟦ f st e ⟧ CT.now)


_∞>>=_ :  ∀ {i A B E} → ∞CCTree E A i → (A → CCTree E B i) → ∞CCTree E B i
force (x ∞>>= f) = force x >>= f



_>>_ : ∀ {i A B E} → CCTree E A i → CCTree E B i → CCTree E B i
p >> q = p >>= λ _ → q

-- Monadic return operator

return : ∀ {i A E} → A → CCTree E A i
return = now

-- Functorial map operator derived from >>=

map : ∀ {i A B E} → (A → B) → CCTree E A i → CCTree E B i
map f p = p >>= (λ x → return (f x))


mutual
  never : ∀ {i A E} -> CCTree E A i
  never = later ∞never

  ∞never : ∀ {i A E} -> ∞CCTree E A i
  force ∞never = never

------------
-- interp --
------------

-- This is the standard effect interpretation function (without
-- state).

interp : ∀ {i A E} {{_ : Concurrent E}} → (∀ {B} → E B → CCTree E B ∞) → CCTree E A i → CCTree E A i
interp f = interpSt tt (λ s x → map (λ y → y , tt) (f x))


-- well-formedness properties

~icong : ∀ {E A B i}{{_ : Concurrent E}} (p : CCTree E A ∞) {k k' : A → CTree E B ∞}
  (b : ∀ x → k x CT.~[ i ] k' x) → ⟦ p ⟧ k CT.~[ i ] ⟦ p ⟧ k'
~icong {i = 0} _ _ = CT.~izero
~icong (now' v) b = b v
~icong {i = suc i} (later' p) b = CT.~ilater (~icong {i = i} (force p) (λ x → CT.~isuc (b x)))
~icong (p ⊕' q) b = CT.⊕-cong (~icong p b) (~icong q b)
~icong ∅' b = CT.~irefl
~icong (eff' e c) b = CT.~ieff e (λ r → ~icong (c r) b)
~icong (p >>=' f) b = ~icong p λ r → ~icong (f r) b
~icong (p ∥⃗' q) b = CT.∥⃗-cong-r (~icong q b)
~icong (interpSt' s f p) b = CT.>>=-cong-r (CT.interpSt s f (⟦ p ⟧ CT.now)) b


~icong-map : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞) {f : B → C} → {k : A → CTree E B ∞} →
  CT.map f (⟦ p ⟧ k)  CT.~[ i ] ⟦ p ⟧ (λ r → CT.map f (k r))
~icong-map {i = 0} _ = CT.~izero
~icong-map (now' v) = CT.~irefl
~icong-map {i = suc i} (later' p) = CT.~ilater (~icong-map {i = i} (force p))
~icong-map (p ⊕' q) = CT.⊕-cong (~icong-map p) (~icong-map q)
~icong-map ∅' = CT.~irefl
~icong-map (eff' e c) = CT.~ieff e (λ r → ~icong-map (c r))
~icong-map (p >>=' g) = CT.~itrans (~icong-map p) (~icong p (λ r → ~icong-map (g r))) 
~icong-map (p ∥⃗' q) = CT.~itrans (CT.∥⃗-map-r (⟦ p ⟧ CT.now) _) (CT.∥⃗-cong-r (~icong-map q))
~icong-map (interpSt' s h p) = CT.>>=-assoc (CT.interpSt s h (⟦ p ⟧ CT.now))
