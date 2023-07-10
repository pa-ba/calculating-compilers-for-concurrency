{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel.Congruence where

open import CTree.IndexedBisimilarity.Parallel.Decomposition
open import CTree.IndexedBisimilarity.Bind
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)


------------------------
-- congruence for par --
------------------------


∥-cong : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥ q ~[ i ] p' ∥ q'
∥-cong  = prf (<×⇐⁺×⇐⁺-wf _) where

  ~i-lsuc : ∀ {i E E' A A'} {l : label E' A'} {p q : CTree' E A} → p ~̂[ suc i ] q → p ~̂[ lsuc l i ] q
  ~i-lsuc b = ~idown (lsuc≤suc _ _) b

  prf : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞} →
    (ac : Acc (×-Lex _≡_ _<_ (×-Lex _≡_ _⇐⁺_ _⇐⁺_)) (i , (p ↑ , q ↑))) → p ~[ i ] p' → q ~[ i ] q'
      → p ∥ q ~[ i ] p' ∥ q'
  prf {zero} _ ~p ~q = ~izero
  prf {suc i} {p = p} {p'} {q} {q'} (acc rec) ~p ~q = ~istep left right where
    left : ∀ {l p''} → (p ∥ q) ↑ [ l ]⇒ p'' →
      ∃[ q'' ] (p' ∥ q') ↑ [ l ]⇒ q'' × p'' ~̂[ lsuc l i ] q''
    left tr with ∥-step tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with q'' , tr'' , b ← ~ileft ~p tr'
               with p''' , refl ← ⇒-ε-wait tr' with q''' , refl ← ⇒-ε-wait tr''
                = -, ∥-stepLeft (LS rf tr'') ,
                  ~iwait λ r → prf (rec _ (inj₂ ( refl , inj₁ ( ( -, ⇒-inp r _) ∷ [ -, tr' ]))))
                    (~iwait' b r) (~i-lsuc {l = l'} ~q)
    ... | inj₁ (inj₁ (LS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with q'' , tr'' , b ← ~ileft ~p tr'
        with p''' , refl ← ⇒-τ-↑ tr' with q''' , refl ← ⇒-τ-↑ tr''
                = _ , ∥-stepLeft (LS rf tr'') ,
                    prf (rec _ (inj₁ ≤-refl)) b (~i-lsuc {l = l'} ~q)
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with p'' , tr'' , b ← ~ileft ~q tr'
               with q''' , refl ← ⇒-ε-wait tr' with p''' , refl ← ⇒-ε-wait tr''
                = -, ∥-stepRight (RS rf tr'') ,
                  ~iwait λ r → prf (rec _ (inj₂ (refl , inj₂ (refl , ( -, ⇒-inp r _) ∷ [ -, tr' ]))))
                    (~i-lsuc {l = l'} ~p) (~iwait' b r) 
    ... | inj₁ (inj₂ (RS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with p'' , tr'' , b ← ~ileft ~q tr'
        with q''' , refl ← ⇒-τ-↑ tr' with p''' , refl ← ⇒-τ-↑ tr''
                = _ , ∥-stepRight (RS rf tr'') ,
                    prf (rec _ (inj₁ ≤-refl)) (~i-lsuc {l = l'} ~p) b
    ... | inj₂ (BSRet tr1 tr2)
      with _ , tr1' , b1 ← ~ileft ~p tr1 | _ , tr2' , b2 ← ~ileft ~q tr2
        =  _ ,  ∥-stepBoth (BSRet tr1' tr2') , ~irefl
    ... | inj₂ (BSSync {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr)
      with _ , tr1' , b1 ← ~ileft ~p tr1 | _ , tr2' , b2 ← ~ileft ~q tr2
           with _ , refl ← ⇒-ε-wait tr1' | _ , refl ← ⇒-ε-wait tr2'
        = _ ,  ∥-stepBoth (BSSync tr1' tr2' tr) , ~isuc (prf (rec _ (inj₂ (refl , inj₁ ( ( -, ⇒-inp _ _) ∷ [ -, tr1 ])))) (~iwait' (b1) v1) (~iwait' (b2) v2))
    right : ∀ {l q''} → (p' ∥ q') ↑ [ l ]⇒ q'' →
      ∃[ p'' ] (p ∥ q) ↑ [ l ]⇒ p'' × p'' ~̂[ lsuc l i ] q''
    right tr with ∥-step tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with q'' , tr'' , b ← ~iright ~p tr'
               with p''' , refl ← ⇒-ε-wait tr' with q''' , refl ← ⇒-ε-wait tr''
                = -, ∥-stepLeft (LS rf tr'') ,
                  ~iwait λ r → prf (rec _ (inj₂ ( refl , inj₁ ( ( -, ⇒-inp r _) ∷ [ -, tr'' ]))))
                    (~iwait' b r) (~i-lsuc {l = l'} ~q)
    ... | inj₁ (inj₁ (LS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with q'' , tr'' , b ← ~iright ~p tr'
        with p''' , refl ← ⇒-τ-↑ tr' with q''' , refl ← ⇒-τ-↑ tr''
                = _ , ∥-stepLeft (LS rf tr'') ,
                    prf (rec _ (inj₁ ≤-refl)) b (~i-lsuc {l = l'} ~q)
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with p'' , tr'' , b ← ~iright ~q tr'
               with q''' , refl ← ⇒-ε-wait tr' with p''' , refl ← ⇒-ε-wait tr''
                = -, ∥-stepRight (RS rf tr'') ,
                  ~iwait λ r → prf (rec _ (inj₂ (refl , inj₂ (refl , ( -, ⇒-inp r _) ∷ [ -, tr'' ]))))
                    (~i-lsuc {l = l'} ~p) (~iwait' b r) 
    ... | inj₁ (inj₂ (RS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with p'' , tr'' , b ← ~iright ~q tr'
        with q''' , refl ← ⇒-τ-↑ tr' with p''' , refl ← ⇒-τ-↑ tr''
                = _ , ∥-stepRight (RS rf tr'') ,
                    prf (rec _ (inj₁ ≤-refl)) (~i-lsuc {l = l'} ~p) b
    ... | inj₂ (BSRet tr1 tr2)
      with _ , tr1' , b1 ← ~iright ~p tr1 | _ , tr2' , b2 ← ~iright ~q tr2
        =  _ ,  ∥-stepBoth (BSRet tr1' tr2') , ~irefl
    ... | inj₂ (BSSync {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr)
      with _ , tr1' , b1 ← ~iright ~p tr1 | _ , tr2' , b2 ← ~iright ~q tr2
           with _ , refl ← ⇒-ε-wait tr1' | _ , refl ← ⇒-ε-wait tr2'
        =  _ ,  ∥-stepBoth (BSSync tr1' tr2' tr) ,  ~isuc (prf (rec _ (inj₂ (refl , inj₁ ( ( -, ⇒-inp _ _) ∷ [ -, tr1' ])))) (~iwait' b1 v1) (~iwait' b2 v2))
           

------------------------------------
-- Corresponding properties for ∥⃗ --
------------------------------------

∥⃗-cong : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥⃗ q ~[ i ] p' ∥⃗ q'
∥⃗-cong ~p ~q = map-cong (∥-cong ~p ~q)

∥⃗-cong-l : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q : CTree E B ∞}
  → p ~[ i ] p' → p ∥⃗ q ~[ i ] p' ∥⃗  q
∥⃗-cong-l b = ∥⃗-cong b ~irefl

∥⃗-cong-r : ∀ {i A B E} {{_ : Concurrent E}} {p : CTree E A ∞}{q q' : CTree E B ∞}
  → q ~[ i ] q' → p ∥⃗ q ~[ i ] p ∥⃗ q'
∥⃗-cong-r b = ∥⃗-cong ~irefl b
