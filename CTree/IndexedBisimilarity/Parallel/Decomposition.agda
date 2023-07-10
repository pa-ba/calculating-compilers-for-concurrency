{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel.Decomposition where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.Bind
open import CTree.Parallel public
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infixl 7 _∥₁_
infixl 7 _∥₂_

_∥₁_ : ∀ {A B E} {{_ : Concurrent E}} → CTree' E A → CTree E B ∞ → CTree' E (A × B)
p ↑ ∥₁ q = (p ∥ q) ↑
wait B p ∥₁ q = wait B λ r → p r ∥ q

_∥₂_ : ∀ {A B E} {{_ : Concurrent E}} → CTree E A ∞ → CTree' E B → CTree' E (A × B)
p ∥₂ q ↑ = (p ∥ q) ↑
p ∥₂ wait B q = wait B λ r → p ∥ q r


data LeftStep {A B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (l : label E (A × B))
              : CTree' E (A × B) → Set₁ where
  LS : ∀ {l' : label E A} {p'} → retFree l l' → p ↑ [ l' ]⇒ p' → LeftStep p q l (p' ∥₁ q)
  
data RightStep {A B E}  {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (l : label E (A × B))
               : CTree' E (A × B) → Set₁ where
  RS : ∀ {l' : label E B} {q'} → retFree l l' → q ↑ [ l' ]⇒ q' → RightStep p q l (p ∥₂ q')

data BothStep {A B E} {{P : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
              : label E (A × B) → CTree' E (A × B) → Set₁ where
  BSRet : ∀ {v1 v2 p' q'} → (tr1 : p ↑ [ ⟨ ρ v1 ⟩ ]⇒ p') → (tr2 : q ↑ [ ⟨ ρ v2 ⟩ ]⇒ q')
        → BothStep p q ⟨ ρ (v1 , v2) ⟩ (∅ ↑)
  BSSync : ∀ {R1 R2 p' q' v1 v2} {e1 : E R1} {e2 : E R2} → 
    (tr1 : p ↑ [ ⟨ ε e1 ⟩ ]⇒ wait _ p') → (tr2 : q ↑ [ ⟨ ε e2 ⟩ ]⇒ wait _ q')
    → (tr : (Concurrent._⇄_ P e1 e2) ↑ [ τ ]⇒ return (v1 , v2) ↑)
      → BothStep p q τ ((p' v1 ∥ q' v2)↑)


leftStep-ρ : ∀ {A B E} {{_ : Concurrent E}} {p : CTree E A ∞} {q : CTree E B ∞} {v r} → ¬ LeftStep p q ⟨ ρ v ⟩ r
leftStep-ρ (LS () _)

rightStep-ρ : ∀ {A B E} {{_ : Concurrent E}} {p : CTree E A ∞} {q : CTree E B ∞} {v r} → ¬ RightStep p q ⟨ ρ v ⟩ r
rightStep-ρ (RS () _)


bsLeft2 : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞} {q1 q2 : CTree E B ∞} →
  BothStep p q1 l r → BothStep p (q1 ⊕ q2) l r
bsLeft2 (BSRet tr1 tr2) = BSRet tr1 (⇒-⊕-l tr2)
bsLeft2 (BSSync tr1 tr2 tr) = BSSync tr1 (⇒-⊕-l tr2) tr

bsRight2 : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞} {q1 q2 : CTree E B ∞} →
  BothStep p q2 l r → BothStep p (q1 ⊕ q2) l r
bsRight2 (BSRet tr1 tr2) = BSRet tr1 (⇒-⊕-r tr2)
bsRight2 (BSSync tr1 tr2 tr) = BSSync tr1 (⇒-⊕-r tr2) tr



bsLeft1 : ∀ {A B E l r} {{_ : Concurrent E}} {p1 p2 : CTree E A ∞} {q : CTree E B ∞} →
  BothStep p1 q l r → BothStep (p1 ⊕ p2) q l r
bsLeft1 (BSRet tr1 tr2) = BSRet (⇒-⊕-l tr1) tr2
bsLeft1 (BSSync tr1 tr2 tr) = BSSync (⇒-⊕-l tr1) tr2 tr


bsRight1 : ∀ {A B E l r} {{_ : Concurrent E}} {p1 p2 : CTree E A ∞} {q : CTree E B ∞} →
  BothStep p2 q l r → BothStep (p1 ⊕ p2) q l r
bsRight1 (BSRet tr1 tr2) = BSRet (⇒-⊕-r tr1) tr2
bsRight1 (BSSync tr1 tr2 tr) = BSSync (⇒-⊕-r tr1) tr2 tr

⇄->>=-step : ∀ {E A1 A2 B l} {{_ : Concurrent E}} (e1 : E A1) (e2 : E A2) {q : CTree' E B } (k : A1 × A2 → CTree E B ∞) →
  ((e1 ⇄ e2) >>= k) ↑  [ l ]⇒ q → (∃[ v ] l ≡ τ × ((e1 ⇄ e2) ↑ [ τ ]⇒ return v ↑ × q ≡ k v ↑))
⇄->>=-step e1 e2 k tr with >>=-step ((e1 ⇄ e2)↑) k tr
... | inj₁ (v ,  tr1 , tr2) with () ← ⇄-τ e1 e2  tr1
... | inj₂ (l , retFreeε , p , tr' , refl)  with () ← ⇄-τ e1 e2 tr'
... | inj₂ (l , retFreeι , p , tr' , refl)  with () ← ⇄-τ e1 e2 tr'
... | inj₂ (l , retFreeτ , p , tr' , refl) with ⇄-return e1 e2 tr'
... | v , refl = v , refl , tr' , refl

∥-step : ∀ {A B E} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} {r : CTree' E (A × B)}
        {l : label E (A × B)} → (p ∥ q) ↑ [ l ]⇒ r →
        (LeftStep p q l r ⊎ RightStep p q l r) ⊎ BothStep p q l r
∥-step (⇒-⊕-l (⇒-⊕-l tr)) = inj₁ (inj₁ (leftStep tr)) where
  leftStep : ∀ {A B E} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} {r : CTree' E (A × B)}
    {l : label E (A × B)} →  (p ⦉ q) ↑ [ l ]⇒ r → LeftStep p q l r
  leftStep {p = later p} ⇒-later = LS retFreeτ  ⇒-later
  leftStep {p = p1 ⊕ p2} (⇒-⊕-l tr) with LS rf tr' ← leftStep tr = LS rf (⇒-⊕-l tr')
  leftStep {p = p1 ⊕ p2} (⇒-⊕-r tr) with LS rf tr' ← leftStep tr = LS rf (⇒-⊕-r tr')
  leftStep {p = eff e c} (⇒-eff .e c') = LS retFreeε (⇒-eff e c)
∥-step (⇒-⊕-l (⇒-⊕-r tr)) = inj₁ (inj₂ (rightStep tr)) where
  rightStep : ∀ {A B E} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} {r : CTree' E (A × B)}
    {l : label E (A × B)} → (p ⦊ q) ↑ [ l ]⇒ r → RightStep p q l r
  rightStep {q = later q} ⇒-later = RS retFreeτ ⇒-later
  rightStep {q = q1 ⊕ q2} (⇒-⊕-l tr) with RS rf tr'  ← rightStep tr = RS rf (⇒-⊕-l tr')
  rightStep {q = q1 ⊕ q2} (⇒-⊕-r tr) with RS rf tr' ← rightStep tr = RS rf (⇒-⊕-r tr')
  rightStep {q = eff e c} (⇒-eff .e c') = RS retFreeε (⇒-eff e c)
∥-step {p = p} {q} (⇒-⊕-r tr) = inj₂ (bothStep p q tr) where
  bothStep : ∀ {A B E} {{_ : Concurrent E}}  (p : CTree E A ∞)(q : CTree E B ∞) {r : CTree' E (A × B)}
    {l : label E (A × B)} → ((p ⋈ q) ↑) [ l ]⇒ r → BothStep p q l r
  bothStep (now v) (now w) (⇒-now _) = BSRet (⇒-now v) (⇒-now w)
  bothStep p@(now v) (q1 ⊕ q2) (⇒-⊕-l tr) = bsLeft2 (bothStep p q1 tr)
  bothStep p@(now v) (q1 ⊕ q2) (⇒-⊕-r tr) = bsRight2 (bothStep p q2 tr)
  bothStep p@(later p') (q1 ⊕ q2) (⇒-⊕-l tr) = bsLeft2 (bothStep p q1 tr)
  bothStep p@(later p') (q1 ⊕ q2) (⇒-⊕-r tr) = bsRight2 (bothStep p q2 tr)
  bothStep (p1 ⊕ p2) q (⇒-⊕-l tr) = bsLeft1 (bothStep p1 q tr)
  bothStep (p1 ⊕ p2) q (⇒-⊕-r tr) = bsRight1 (bothStep p2 q tr)
  bothStep p@∅ (q1 ⊕ q2) (⇒-⊕-l tr) with BSRet () tr2 ← bothStep p q1 tr
  bothStep p@∅ (q1 ⊕ q2) (⇒-⊕-r tr) with BSRet () tr2 ← bothStep p q2 tr
  bothStep p@(eff e c) (q1 ⊕ q2) (⇒-⊕-l tr) = bsLeft2 (bothStep p q1 tr)
  bothStep p@(eff e c) (q1 ⊕ q2) (⇒-⊕-r tr) = bsRight2 (bothStep p q2 tr)
  bothStep (eff {B = R1} e1 c1) (eff {B = R2} e2 c2)  {r = r} {l = l} tr
    with ⇄->>=-step e1 e2 _ tr
  ... | v , refl , tr' , refl = BSSync (⇒-eff e1 c1) (⇒-eff e2 c2) tr'

∥-stepBoth : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} →
  BothStep p q l r  → (p ∥ q) ↑ [ l ]⇒ r
∥-stepBoth tr = ⇒-⊕-r (step tr) where
  step : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} →
    BothStep p q l r  → (p ⋈ q) ↑ [ l ]⇒ r
  step (BSRet (⇒-now _) (⇒-now _)) = ⇒-now _
  step (BSRet (⇒-now _) (⇒-⊕-l tr2)) = ⇒-⊕-l (step (BSRet (⇒-now _) tr2))
  step (BSRet (⇒-now _) (⇒-⊕-r tr2)) = ⇒-⊕-r (step (BSRet (⇒-now _) tr2))
  step (BSRet (⇒-⊕-l tr1) tr2) = ⇒-⊕-l (step (BSRet tr1 tr2))
  step (BSRet (⇒-⊕-r tr1) tr2) = ⇒-⊕-r (step (BSRet tr1 tr2))
  step (BSSync (⇒-eff e1 c1) (⇒-eff e2 c2) tr) = >>=-step2 _ _ retFreeτ tr
  step (BSSync tr1@(⇒-eff _ c) (⇒-⊕-l tr2) tr) = ⇒-⊕-l (step (BSSync tr1 tr2 tr))
  step (BSSync tr1@(⇒-eff _ c) (⇒-⊕-r tr2) tr) = ⇒-⊕-r (step (BSSync tr1 tr2 tr))
  step (BSSync (⇒-⊕-l tr1) tr2 tr) = ⇒-⊕-l (step (BSSync tr1 tr2 tr))
  step (BSSync (⇒-⊕-r tr1) tr2 tr) = ⇒-⊕-r (step (BSSync tr1 tr2 tr))




∥-stepLeft : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞}
  → LeftStep p q l r  → (p ∥ q) ↑ [ l ]⇒ r
∥-stepLeft tr = ⇒-⊕-l (⇒-⊕-l (step tr)) where
  step : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞}
    → LeftStep p q l r  → (p ⦉ q) ↑ [ l ]⇒ r
  step {p = now v} (LS () (⇒-now .v))
  step {p = later p} (LS retFreeτ ⇒-later) = ⇒-later
  step {p = p ⊕ p₁} (LS rf (⇒-⊕-l tr)) = ⇒-⊕-l (step (LS rf tr))
  step {p = p ⊕ p₁} (LS rf (⇒-⊕-r tr)) = ⇒-⊕-r (step (LS rf tr))
  step {p = eff e c} (LS retFreeε (⇒-eff .e .c)) = ⇒-eff e _



∥-stepRight : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} 
  → RightStep p q l r → (p ∥ q) ↑ [ l ]⇒ r
∥-stepRight tr = ⇒-⊕-l (⇒-⊕-r (step tr)) where
  step : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} 
    → RightStep p q l r → (p ⦊ q) ↑ [ l ]⇒ r
  step {q = now v} (RS () (⇒-now .v))
  step {q = later q} (RS retFreeτ ⇒-later) = ⇒-later
  step {q = p ⊕ p₁} (RS rf (⇒-⊕-l tr)) = ⇒-⊕-l (step (RS rf tr))
  step {q = p ⊕ p₁} (RS rf (⇒-⊕-r tr)) = ⇒-⊕-r (step (RS rf tr))
  step {q = eff e c} (RS retFreeε (⇒-eff .e .c)) = ⇒-eff e _

_∥₃_ : ∀ {A B E} {{_ : Concurrent E}} → CTree' E A → CTree' E B → CTree' E (A × B)
(p ↑) ∥₃ q = p ∥₂ q
p ∥₃(q ↑) = p ∥₁ q
_ ∥₃ _ = ∅ ↑

