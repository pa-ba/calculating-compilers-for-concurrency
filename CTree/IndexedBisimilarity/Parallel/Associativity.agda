{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel.Associativity where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.Bind public
open import CTree.IndexedBisimilarity.Parallel.Decomposition

open import Data.Nat
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

-------------------------
-- associativity for ∥⃗ --
-------------------------

infixl 7 _∥⃗₁_
infixl 7 _∥⃗₂_

_∥⃗₁_ : ∀ {A B E} {{_ : Concurrent E}} → CTree' E A → CTree E B ∞ → CTree' E B
p ∥⃗₁ q = map' proj₂ (p ∥₁ q)

_∥⃗₂_ : ∀ {A B E} {{_ : Concurrent E}} → CTree E A ∞ → CTree' E B → CTree' E B
p ∥⃗₂ q = map' proj₂ (p ∥₂ q)  


data LeftStep' {A B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (l : label E B)
              : CTree' E B → Set₁ where
     LS' : ∀ {l' : label E A} {p'} → retFree l l' → p ↑ [ l' ]⇒ p' → LeftStep' p q l (p' ∥⃗₁ q)
    
data RightStep' {A B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (l : label E B)
                 : CTree' E B → Set₁ where
    RS' : ∀ {l' : label E B} {q'} → retFree l l' → q ↑ [ l' ]⇒ q' → RightStep' p q l (p ∥⃗₂ q')


data BothStep' {A B E} {{P : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
              : label E B → CTree' E B → Set₁ where
  BSRet' : ∀ {v1 v2 p' q'} → (tr1 : p ↑ [ ⟨ ρ v1 ⟩ ]⇒ p') → (tr2 : q ↑ [ ⟨ ρ v2 ⟩ ]⇒ q')
        → BothStep' p q ⟨ ρ v2 ⟩ (∅ ↑)
  BSSync' : ∀ {R1 R2 p' q' v1 v2} {e1 : E R1} {e2 : E R2} → 
    (tr1 : p ↑ [ ⟨ ε e1 ⟩ ]⇒ wait _ p') → (tr2 : q ↑ [ ⟨ ε e2 ⟩ ]⇒ wait _ q')
    → (tr : (Concurrent._⇄_ P e1 e2) [ τ ]=> return (v1 , v2))
      → BothStep' p q τ ((p' v1 ∥⃗ q' v2)↑)

∥⃗-step : ∀ {A B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {r : CTree' E B}
          {l : label E B} → (p ∥⃗ q) ↑ [ l ]⇒ r →
          (LeftStep' p q l r ⊎ RightStep' p q l r) ⊎ BothStep' p q l r
∥⃗-step p q tr with map-step ((p ∥ q)↑) proj₂ tr
... | inj₁ (v , tr' , refl) with ∥-step tr'
... | inj₁ (inj₁ ls) with () ← leftStep-ρ ls
... | inj₁ (inj₂ rs) with () ← rightStep-ρ rs
... | inj₂ (BSRet tr1 tr2) rewrite ⇒-ρ-∅ tr = inj₂ (BSRet' tr1 tr2)
∥⃗-step p q tr | inj₂ (l' , rf , p' , tr' , refl) with ∥-step tr'
... | inj₁ (inj₁ (LS rf' tr'')) = inj₁ (inj₁ (LS' (retFree-trans rf rf') tr''))
... | inj₁ (inj₂ (RS rf' tr'')) = inj₁ (inj₂ (RS' (retFree-trans rf rf') tr''))
∥⃗-step p q tr | inj₂ (l' , retFreeτ , p' , tr' , refl) | inj₂ (BSSync x tr1 tr2)
  = inj₂ (BSSync' x tr1  tr2)

∥⃗-stepBoth : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} →
    BothStep' p q l r  → (p ∥⃗ q) ↑ [ l ]⇒ r
∥⃗-stepBoth (BSRet' tr1 tr2) = map-step1 proj₂ (∥-stepBoth (BSRet tr1 tr2))
∥⃗-stepBoth (BSSync' x tr1 tr2) =  map-step2 _ proj₂ retFreeτ (∥-stepBoth (BSSync x tr1 tr2))


∥⃗-stepLeft : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞}
    → LeftStep' p q l r  → (p ∥⃗ q) ↑ [ l ]⇒ r
∥⃗-stepLeft (LS' rf tr) = map-step2 _ proj₂ (coerce-retFree rf) (∥-stepLeft (LS (coerce-retFree' rf) tr))


∥⃗-stepRight : ∀ {A B E l r} {{_ : Concurrent E}} {p : CTree E A ∞}{q : CTree E B ∞} 
    → RightStep' p q l r → (p ∥⃗ q) ↑ [ l ]⇒ r
∥⃗-stepRight (RS' rf tr) = map-step2 _ proj₂ (coerce-retFree rf) (∥-stepRight (RS (coerce-retFree' rf) tr))


leftStepWait : ∀ {A B E R} {{_ : Concurrent E}} {p : CTree E A ∞} {q : CTree E B ∞} {r : CTree' E B} {e : E R}
  → LeftStep' p q ⟨ ε e ⟩ r → ∃[ p' ] p ↑ [ ⟨ ε e ⟩ ]⇒ wait R p' × r ≡ wait R (λ v → p' v ∥⃗ q)
leftStepWait (LS' retFreeε tr) with p' , refl ← ⇒-ε-wait tr = p' , tr , refl

rightStepWait : ∀ {A B E R} {{_ : Concurrent E}} {p : CTree E A ∞} {q : CTree E B ∞} {r : CTree' E B} {e : E R}
  → RightStep' p q ⟨ ε e ⟩ r → ∃[ q' ] q ↑ [ ⟨ ε e ⟩ ]⇒ wait R q' × r ≡ wait R (λ v → p ∥⃗ q' v)
rightStepWait (RS' retFreeε tr) with p' , refl ← ⇒-ε-wait tr = p' , tr , refl



∥⃗-assoc : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (r : CTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] p ∥⃗ (q ∥⃗ r)
∥⃗-assoc p q r = prf p q r (<×⇐⁺×⇐⁺×⇐⁺-wf _) where
  prf : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (r : CTree E C ∞)
        (ac : Acc (×-Lex _≡_ _<_ (×-Lex _≡_ _⇐⁺_ (×-Lex _≡_ _⇐⁺_ _⇐⁺_))) (i , (p ↑ , (q ↑ , r ↑))))
         → (p ∥⃗ q) ∥⃗ r ~[ i ] p ∥⃗ (q ∥⃗ r)
  prf {zero} p q r _ = ~izero
  prf {suc i} p q r (acc rec) = ~istep left right where
    left : ∀ {l p' } → ((p ∥⃗ q ∥⃗ r) ↑) [ l ]⇒ p' → ∃[ q' ] ((p ∥⃗ (q ∥⃗ r)) ↑) [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
    left {l} tr with ∥⃗-step (p ∥⃗ q) r tr
    ... | inj₁ (inj₁ (LS' rf tr')) with ∥⃗-step p q tr'
    ... | inj₁ (inj₁ (LS' rf' tr'')) =  _ ,
      ∥⃗-stepLeft (LS' (retFree-trans rf rf') tr'') ,  assoc1 _ (retFree-trans rf rf') tr''  where
      assoc1 : ∀ {l'} p' → retFree l l' → p ↑ [ l' ]⇒ p' → (p' ∥⃗₁ q ∥⃗₁ r) ~̂[ lsuc l i ] (p' ∥⃗₁ (q ∥⃗ r))
      assoc1 {⟨ a ⟩} (p ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₁ [ ( a , tr) ])))
      assoc1 {τ} (p ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
      assoc1 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf (c v) q r
        (rec _ (inj₂ (lsuc-retFree rf _ , inj₁ ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)])))))
      assoc1 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf (c v) q r (rec _ (inj₁ ≤-refl)))
    ... | inj₁ (inj₂ (RS' rf' tr'')) = _ , 
      ∥⃗-stepRight (RS' (coerce-retFree (retFree-trans rf rf'))
        (∥⃗-stepLeft (LS' (coerce-retFree' (retFree-trans rf rf')) tr''))) , assoc21 _ (retFree-trans rf rf') tr'' where
          assoc21 : ∀ {l'} q' → retFree l l' → q ↑ [ l' ]⇒ q' → (p ∥⃗₂ q' ∥⃗₁ r) ~̂[ lsuc l i ] (p ∥⃗₂ (q' ∥⃗₁ r))
          assoc21 {⟨ a ⟩} (q ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₂ (refl , inj₁ [ ( a , tr) ]) )))
          assoc21 {τ} (q ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
          assoc21 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p (c v) r
            (rec _ (inj₂ (lsuc-retFree rf _ , inj₂ (refl , inj₁ ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)]))))))
          assoc21 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p (c v) r (rec _ (inj₁ ≤-refl)))

    left tr | inj₁ (inj₁ (LS' retFreeτ tr')) | inj₂ (BSSync' tr1 tr2 tr'')
      = _ ,  ∥⃗-stepBoth (BSSync' tr1 (∥⃗-stepLeft (LS' retFreeε tr2)) tr'') , prf _ _ r (rec _ (inj₁ ≤-refl))
        
    left {l} tr | inj₁ (inj₂ (RS' rf tr')) = _ , ∥⃗-stepRight (RS' rf (∥⃗-stepRight (RS' (retFree-refl rf) tr'))) ,
                assoc2 _ rf tr' where
      assoc2 : ∀ {l'} r' → retFree l l' → r ↑ [ l' ]⇒ r' → (p ∥⃗ q ∥⃗₂ r') ~̂[ lsuc l i ] (p ∥⃗₂ (q ∥⃗₂ r'))
      assoc2 {⟨ a ⟩} (r ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₂ (refl , inj₂ (refl , [ ( a , tr) ])) )))
      assoc2 {τ} (r ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
      assoc2 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p q (c v)
            (rec _ (inj₂ (lsuc-retFree rf _ , inj₂ (refl , inj₂ (refl , ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)])))))))
      assoc2 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p q (c v) (rec _ (inj₁ ≤-refl)))
    left tr | inj₂ (BSRet' tr1 tr2) with ∥⃗-step p q tr1
    ... | inj₁ (inj₁ (LS' () _))
    ... | inj₁ (inj₂ (RS' () _))
    ... | inj₂ (BSRet' tr3 tr4) = _ , ∥⃗-stepBoth (BSRet' tr3 (∥⃗-stepBoth (BSRet' tr4 tr2))) , ~irefl
    
    left tr | inj₂ (BSSync' tr1 tr2 trl) with ∥⃗-step p q tr1
    ... | inj₁ (inj₁ ls) with (p' , tr' , refl) ← leftStepWait ls
      = _ , ∥⃗-stepBoth (BSSync' tr'  (∥⃗-stepRight (RS' retFreeε tr2)) trl) , prf (p' _) q _ (rec _ (inj₁ ≤-refl)) 
    ... | inj₁ (inj₂ rs) with (q' , tr' , refl) ← rightStepWait rs
      = _ ,  ∥⃗-stepRight (RS' retFreeτ (∥⃗-stepBoth (BSSync' tr' tr2 trl))) , prf p (q' _) _ (rec _ (inj₁ ≤-refl))
    right : ∀ {l q' } → ((p ∥⃗ (q ∥⃗ r)) ↑) [ l ]⇒ q' → ∃[ p' ] ((p ∥⃗ q ∥⃗ r) ↑) [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
    right {l} tr with ∥⃗-step p (q ∥⃗ r) tr
    right {l} tr | inj₁ (inj₂ (RS' rf tr')) with ∥⃗-step q r tr'
    ... | inj₁ (inj₂ (RS' rf' tr'')) = _ ,  ∥⃗-stepRight (RS' (retFree-trans rf rf') tr'')
          , assoc2 _ (retFree-trans rf rf') tr'' where
      assoc2 : ∀ {l'} r' → retFree l l' → r ↑ [ l' ]⇒ r' → (p ∥⃗ q ∥⃗₂ r') ~̂[ lsuc l i ] (p ∥⃗₂ (q ∥⃗₂ r'))
      assoc2 {⟨ a ⟩} (r ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₂ (refl , inj₂ (refl , [ ( a , tr) ])) )))
      assoc2 {τ} (r ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
      assoc2 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p q (c v)
            (rec _ (inj₂ (lsuc-retFree rf _ , inj₂ (refl , inj₂ (refl , ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)])))))))
      assoc2 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p q (c v) (rec _ (inj₁ ≤-refl)))
    ... | inj₁ (inj₁ (LS' rf' tr'')) =  _ , ∥⃗-stepLeft (LS' (coerce-retFree (retFree-trans rf rf'))
        (∥⃗-stepRight (RS' (coerce-retFree' (retFree-trans rf rf')) tr''))) ,  assoc21 _ (retFree-trans rf rf') tr'' where
          assoc21 : ∀ {l'} q' → retFree l l' → q ↑ [ l' ]⇒ q' → (p ∥⃗₂ q' ∥⃗₁ r) ~̂[ lsuc l i ] (p ∥⃗₂ (q' ∥⃗₁ r))
          assoc21 {⟨ a ⟩} (q ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₂ (refl , inj₁ [ ( a , tr) ]) )))
          assoc21 {τ} (q ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
          assoc21 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p (c v) r
            (rec _ (inj₂ (lsuc-retFree rf _ , inj₂ (refl , inj₁ ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)]))))))
          assoc21 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p (c v) r (rec _ (inj₁ ≤-refl)))
    right {_} tr | inj₁ (inj₂ (RS' retFreeτ tr')) | inj₂ (BSSync' tr1 tr2 trl)
      = _ , ∥⃗-stepBoth (BSSync' (∥⃗-stepRight (RS' retFreeε tr1)) tr2 trl) , prf p _ _ (rec _ (inj₁ ≤-refl))
    right {l} tr | inj₁ (inj₁ (LS' rf tr')) = _ ,
          ∥⃗-stepLeft (LS' (coerce-retFree rf) (∥⃗-stepLeft (LS' (coerce-retFree' rf) tr'))) , assoc1 _ rf tr' where
      assoc1 : ∀ {l'} p' → retFree l l' → p ↑ [ l' ]⇒ p' → (p' ∥⃗₁ q ∥⃗₁ r) ~̂[ lsuc l i ] (p' ∥⃗₁ (q ∥⃗ r))
      assoc1 {⟨ a ⟩} (p ↑) rf tr = prf p q r (rec _ (inj₂ ( lsuc-retFree rf _ , inj₁ [ ( a , tr) ])))
      assoc1 {τ} (p ↑) retFreeτ tr = prf p q r (rec _ (inj₁ ≤-refl))
      assoc1 {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf (c v) q r
        (rec _ (inj₂ (lsuc-retFree rf _ , inj₁ ( (( ι v , ⇒-inp v c)) ∷  [(a , tr)])))))
      assoc1 {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf (c v) q r (rec _ (inj₁ ≤-refl)))
    right {_} tr | inj₂ (BSRet' tr1 tr2) with ∥⃗-step q r tr2
    ... | inj₁ (inj₁ (LS' () _))
    ... | inj₁ (inj₂ (RS' () _))
    ... | inj₂ (BSRet' tr3 tr4) = _ , ∥⃗-stepBoth (BSRet' (∥⃗-stepBoth (BSRet' tr1 tr3)) tr4) , ~irefl
    right {_} tr | inj₂ (BSSync' tr1 tr2 trl) with ∥⃗-step q r tr2
    ... | inj₁ (inj₁ ls) with (q' , tr' , refl) ← leftStepWait ls
      = _ , ∥⃗-stepLeft (LS' retFreeτ (∥⃗-stepBoth (BSSync' tr1 tr' trl))) , prf _ (q' _) r (rec _ (inj₁ ≤-refl)) 
    ... | inj₁ (inj₂ rs) with (r' , tr' , refl) ← rightStepWait rs
      = _ , ∥⃗-stepBoth (BSSync' (∥⃗-stepLeft (LS' retFreeε tr1)) tr' trl) , prf _ q (r' _) (rec _ (inj₁ ≤-refl)) 
