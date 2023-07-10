{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.Interp
open import CTree.IndexedBisimilarity.Parallel.Commutativity public
open import CTree.IndexedBisimilarity.Parallel.Decomposition public
open import CTree.IndexedBisimilarity.Parallel.Associativity public
open import CTree.IndexedBisimilarity.Parallel.Congruence public
open import CTree.IndexedBisimilarity.Parallel.Map public
open import Data.Nat
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Function using (id; _∘_)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)
open import Data.Nat.Induction

-- Decomposition, associativity, commutativity, congruence, and map-laws are in
-- separate files, since typechecking is slow.


return-∥⃗ : ∀ {i A B E} {{_ : Concurrent E}} {v : A} {p : CTree E B ∞}
  → return v ∥⃗ p ~[ i ] p
return-∥⃗ = prf (<-wellFounded _) _  where
  prf : ∀ {i A B E} {{_ : Concurrent E}} {v : A} (ac : Acc (_<_) i) (p : CTree E B ∞) → return v ∥⃗ p ~[ i ] p
  prf {zero} _ _ = ~izero
  prf {suc i} {B = B} {E} {v = v} a p = ~istep (left a p) (right a p) where
    left : ∀ {l p'} → (ac : Acc (_<_) (suc i)) → (p : CTree E B ∞)
      → ((return v ∥⃗ p) ↑) [ l ]⇒ p' → ∃[ q' ] (p ↑) [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
    left (acc rec) (later p) (⇒-⊕-l (⇒-⊕-r ⇒-later)) = _ , ⇒-later , prf (rec i ≤-refl) (force p)
    left a (p ⊕ q) (⇒-⊕-l (⇒-⊕-r (⇒-⊕-l tr))) with q' , tr' , b ← left a p (⇒-⊕-l (⇒-⊕-r tr))
      = _ , ⇒-⊕-l tr' , b
    left a (p ⊕ q) (⇒-⊕-l (⇒-⊕-r (⇒-⊕-r tr))) with q' , tr' , b ← left a q (⇒-⊕-l (⇒-⊕-r tr))
      = _ , ⇒-⊕-r tr' , b
    left a (eff e c) (⇒-⊕-l (⇒-⊕-r (⇒-eff .e _))) = _ , ⇒-eff e c , ~iwait (λ r → prf a (c r))
    left _ (now v) (⇒-⊕-r (⇒-now .v)) = _ , ⇒-now v , ~irefl
    left a (p ⊕ q) (⇒-⊕-r (⇒-⊕-l tr)) with q' , tr' , b ← left a p (⇒-⊕-r tr)
      = _ , ⇒-⊕-l tr' , b
    left a (p ⊕ q) (⇒-⊕-r (⇒-⊕-r tr)) with q' , tr' , b ← left a q (⇒-⊕-r tr)
      =  _ , ⇒-⊕-r tr' , b
    right : ∀ {l q'} → (ac : Acc (_<_) (suc i)) → (p : CTree E B ∞)
      → (p ↑) [ l ]⇒ q' → ∃[ p' ] ((return v ∥⃗ p) ↑) [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
    right a (now v) (⇒-now .v) = _ , ⇒-⊕-r (⇒-now v) , ~irefl
    right (acc rec) (later p) ⇒-later = -, ⇒-⊕-l (⇒-⊕-r ⇒-later) , prf (rec i ≤-refl) (force p)
    right a (p ⊕ q) (⇒-⊕-l tr) with right a p tr
    ... | q' , ⇒-⊕-l (⇒-⊕-r tr') , b = -, ⇒-⊕-l (⇒-⊕-r (⇒-⊕-l tr')) , b
    ... | q' , ⇒-⊕-r tr' , b = -, ⇒-⊕-r (⇒-⊕-l tr') , b
    right a (p ⊕ q) (⇒-⊕-r tr) with right a q tr
    ... | q' , ⇒-⊕-l (⇒-⊕-r tr') , b = _ , ⇒-⊕-l (⇒-⊕-r (⇒-⊕-r tr')) , b
    ... | q' , ⇒-⊕-r tr' , b = -, ⇒-⊕-r (⇒-⊕-r tr') , b
    right a (eff e c) (⇒-eff .e .c) = -, ⇒-⊕-l (⇒-⊕-r (⇒-eff e _)) , ~iwait (λ r → prf a (c r))

