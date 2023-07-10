{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CCTree.Transitions where
open import CCTree.Definitions
open import Data.Product hiding (map)
open import Size public
open import Data.Unit
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Data.Bool
import CTree as CT
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Relation.Nullary

-- Generalised choice tree: It is either a choice tree or a choice
-- tree that is waiting for some input
data CCTree' E A : Set₁ where
  _↑ : (p : CCTree E A ∞) → CCTree' E A
  wait : ∀ (B : Set) → (c : B → CCTree E A ∞) → CCTree' E A

⟦_⟧' : ∀ {A E} {{_ : Concurrent E}} → CCTree' E A → ∀ {R} → (A → CTree E R ∞) → CTree' E R
⟦ p ↑ ⟧' c = ⟦ p ⟧ c CT.↑
⟦ wait B c ⟧' c' = CT.wait _ λ r → ⟦ c r ⟧ c'



infix 3 _[_]⇒_
_[_]⇒_ : ∀ {E A} {{_ : Concurrent E}} → CCTree' E A → label E A → CCTree' E A → Set₁
p [ l ]⇒ q = ⟦ p ⟧' CT.now  [ l ]⇒' ⟦ q ⟧' CT.now

private
  ⇒-eff' : ∀ {E A B} {{_ : Concurrent E}} (e : E B) (c : B → CCTree E A ∞) → eff e c ↑ [ ⟨ ε e ⟩ ]⇒ wait B c
  ⇒-eff' e c = CT.⇒-eff e _
  
  ⇒-inp' : ∀ {E A B}  {{_ : Concurrent E}} (r : B) (c : B → CCTree E A ∞) → wait B c [ ⟨ ι r ⟩ ]⇒ c r ↑
  ⇒-inp' r c = CT.⇒-inp r _

  ⇒-now' : ∀ {E A}  {{_ : Concurrent E}} (v : A) → now v ↑ [ ⟨ ρ v ⟩ ]⇒ ∅ {E = E} ↑
  ⇒-now' v = CT.⇒-now v
  
  ⇒-⊕-l' : ∀ {E A}  {{_ : Concurrent E}}  {l p} {p1 p2 : CCTree E A ∞} → p1 ↑ [ l ]⇒ p → (p1 ⊕ p2) ↑ [ l ]⇒ p 
  ⇒-⊕-l' tr = CT.⇒-⊕-l tr

  ⇒-⊕-r' : ∀ {E A}  {{_ : Concurrent E}}  {l p} {p1 p2 : CCTree E A ∞} → p2 ↑ [ l ]⇒ p → (p1 ⊕ p2) ↑ [ l ]⇒ p 
  ⇒-⊕-r' tr = CT.⇒-⊕-r tr

  ⇒-later' : ∀ {E A}  {{_ : Concurrent E}} {p : ∞CCTree E A ∞} → later p ↑ [ τ ]⇒ force p ↑
  ⇒-later' = CT.⇒-later



infix 3 _[_]=>_
_[_]=>_  : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → label E A → CCTree E A ∞ → Set₁
p [ l ]=> q = ⟦ p ⟧ CT.now [ l ]=>' ⟦ q ⟧ CT.now

infix 3 _[_]=>!_
_[_]=>!_  : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → label E A → CCTree E A ∞ → Set₁
p [ l ]=>! q = Σ[ tr ∈ p [ l ]=> q ] ((tr' : p [ l ]=> q) → tr ≡ tr')


infix 3 _[_,_]==>_
_[_,_]==>_  : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → label E A → label E A → CCTree E A ∞ → Set₁
p [ l , l' ]==> q = ∃[ p' ] (⟦ p ⟧ CT.now) CT.↑ [ l ]⇒' p' × p' [ l' ]⇒' (⟦ q ⟧ CT.now) CT.↑

_[_]⇒ : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → label E A → Set₁
p [ l ]⇒ = ∃[ q ] ⟦ p ⟧ CT.now CT.↑ [ l ]⇒' q

_[_]⇏ : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → label E A → Set₁
p [ l ]⇏ = ∀ {q} → ¬ (⟦ p ⟧ CT.now CT.↑ [ l ]⇒' q)


_⇏ : ∀ {A E} {{_ : Concurrent E}} → CCTree E A ∞ → Set₁
p ⇏ = ∀ {l} → p [ l ]⇏
