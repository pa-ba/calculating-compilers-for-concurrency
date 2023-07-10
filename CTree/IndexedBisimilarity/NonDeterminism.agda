{-# OPTIONS --sized-types #-}

--------------------------
-- non-determinism laws --
--------------------------


module CTree.IndexedBisimilarity.NonDeterminism where

open import CTree.IndexedBisimilarity.BasicProperties public
open import Data.Nat
open import Data.Product


⊕-unit-l : ∀ {i E A} {p : CTree E A ∞} → ∅ ⊕ p ~[ i ] p
⊕-unit-l {zero} = ~izero
⊕-unit-l {suc i} {p = p} = ~istep left right where
  left : ∀ {l p'} → (∅ ⊕ p) ↑ [ l ]⇒ p' → ∃[ q' ] p ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-r trans') = _ , trans' , ~irefl
  right : ∀ {l q'} → p ↑ [ l ]⇒ q' → ∃[ p' ] (∅ ⊕ p) ↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right trans = _ , ⇒-⊕-r trans , ~irefl

 
⊕-assoc : ∀ {i E A} {p q r : CTree E A ∞} → (p ⊕ q) ⊕ r ~[ i ] p ⊕ (q ⊕ r)
⊕-assoc {zero} = ~izero
⊕-assoc {suc i} {p = p} {q} {r} = ~istep left right where
  left : ∀ {l p'} → (p ⊕ q ⊕ r)↑ [ l ]⇒ p' → ∃[ q' ] (p ⊕ (q ⊕ r))↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l (⇒-⊕-l tr)) =  _ , ⇒-⊕-l tr , ~irefl
  left (⇒-⊕-l (⇒-⊕-r tr)) = _ , ⇒-⊕-r (⇒-⊕-l tr) , ~irefl
  left (⇒-⊕-r tr) =  _ ,  ⇒-⊕-r (⇒-⊕-r tr) , ~irefl
  right : ∀ {l q'} → (p ⊕ (q ⊕ r))↑ [ l ]⇒ q' → ∃[ p' ] (p ⊕ q ⊕ r)↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right (⇒-⊕-r (⇒-⊕-r tr)) =  _ , ⇒-⊕-r tr , ~irefl
  right (⇒-⊕-r (⇒-⊕-l tr)) = _ , ⇒-⊕-l (⇒-⊕-r tr) , ~irefl
  right (⇒-⊕-l tr) =  _ ,  ⇒-⊕-l (⇒-⊕-l tr) , ~irefl

⊕-idem : ∀ {i E A} {p : CTree E A ∞} → p ⊕ p ~[ i ] p
⊕-idem {zero} = ~izero
⊕-idem {suc i} {p = p} = ~istep left  λ tr →  _ , ⇒-⊕-l tr , ~irefl  where
  left : ∀ {l p'} → (p ⊕ p)↑ [ l ]⇒ p' → ∃[ q' ] p ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l tr) =  _ , tr , ~irefl
  left (⇒-⊕-r tr) = _ , tr , ~irefl

⊕-comm : ∀ {i E A} {p q : CTree E A ∞} → p ⊕ q ~[ i ] q ⊕ p
⊕-comm {zero} = ~izero
⊕-comm {suc i} {p = p} {q} = ~istep left right where
  left : ∀ {l p'} → (p ⊕ q)↑ [ l ]⇒ p' → ∃[ q' ] (q ⊕ p)↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l tr) =  _ , ⇒-⊕-r tr , ~irefl
  left (⇒-⊕-r tr) = _ , ⇒-⊕-l tr , ~irefl
  right : ∀ {l q'} → (q ⊕ p)↑ [ l ]⇒ q' → ∃[ p' ] (p ⊕ q)↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right (⇒-⊕-l tr) =  _ , ⇒-⊕-r tr , ~irefl
  right (⇒-⊕-r tr) = _ , ⇒-⊕-l tr , ~irefl

⊕-unit-r : ∀ {i E A} {p : CTree E A ∞} → p ⊕ ∅ ~[ i ] p
⊕-unit-r = ~itrans ⊕-comm ⊕-unit-l

⊕-distr : ∀ {i E A B} (p q : CTree E A ∞) {f : A → CTree E B ∞}
  → (p ⊕ q) >>= f ~[ i ] (p >>= f) ⊕ (q >>= f)
⊕-distr _ _ = ~irefl
