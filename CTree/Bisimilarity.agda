{-# OPTIONS --copatterns --sized-types #-}

----------------------------------
-- Bisimilarity of choice trees --
----------------------------------


module CTree.Bisimilarity where

open import CTree.IndexedBisimilarity
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Induction.WellFounded
open import Data.Product.Relation.Binary.Lex.Strict

--------------------------------------------------------------------
-- This is the definition of (strong) bisimilarity of (generalised)
-- choice trees in terms of their LTS semantics.
--------------------------------------------------------------------

infix 3 _~̂_

record _~̂_  {E A} (p q : CTree' E A) {i : Size} : Set₁ where
  coinductive
  constructor bisim
  field
    ~-left : ∀ {l p'} {j : Size< i}  → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × (p' ~̂ q') {j})
    ~-right : ∀ {l q'} {j : Size< i} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × (p' ~̂ q') {j})

open _~̂_ public

infix 3 _~_

_~_ : ∀ {E A} → CTree E A ∞ → CTree E A ∞ → Set₁
p ~ q = p ↑ ~̂ q ↑


---------------------------------------------------------------------
-- We show that indexed bisimilarity is (classically) equivalent to
-- bisimilarity.
---------------------------------------------------------------------



-- bisimilarity ⇒ indexed bisimilarity

~-~i : ∀ {E A i} {p q : CTree' E A} → (p ~̂ q) → p ~̂[ i ] q
~-~i = prf (<×⇐-wf _) where
  prf : ∀ {E A i} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → (p ~̂ q) → p ~̂[ i ] q
  prf {i = zero} _ b = ~izero
  prf {i = suc i} {p} {q} (acc rec) b = ~istep left right where
    left : ∀ {l p'} → p [ l ]⇒ p' → ∃-syntax (λ q' → q [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')
    left {⟨ x ⟩} {p'} tr with q' , tr' , b' ← ~-left b tr = q' , tr' , prf (rec (suc i , p') (inj₂ (refl , _ , tr))) b'
    left {τ} {p'} tr with q' , tr' , b' ← ~-left b tr = q' , tr' , prf ( rec (i , p') (inj₁ ≤-refl)) b'
    right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] p [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
    right {⟨ x ⟩} {q'} tr with p' , tr' , b' ← ~-right b tr = p' , tr' , prf (rec (suc i , p') (inj₂ (refl , _ , tr'))) b'
    right {τ} {q'} tr with p' , tr' , b' ← ~-right b tr = p' , tr' , prf (rec (i , p') (inj₁ ≤-refl)) b'



-- Next we show that indexed bisimilarity implies bisimilarity. To
-- this end we need a number of lemmas.

private
  ¬~ileft : ∀ {E A l i} {p p' q : CTree' E A} → p [ l ]⇒ p' →
          (∀ {q'} → q [ l ]⇒ q' → ¬ (p' ~̂[ i ] q')) → ¬ (p ~̂[ suc i ] q)
  ¬~ileft {l = ⟨ a ⟩} tr step bi with q' , tr' , bi' ← ~ileft bi tr = step tr' (~idown (n≤1+n _) bi')
  ¬~ileft {l = τ} tr step bi with q' , tr' , bi' ← ~ileft bi tr = step tr' bi'

  ¬~iright : ∀ {E A l i} {p q q' : CTree' E A} → q [ l ]⇒ q' →
           (∀ {p'} → p [ l ]⇒ p' → ¬ (p' ~̂[ i ] q')) → ¬ (p ~̂[ suc i ] q)
  ¬~iright {l = ⟨ a ⟩} tr step bi with q' , tr' , bi' ← ~iright bi tr = step tr' (~idown (n≤1+n _) bi')
  ¬~iright {l = τ} tr step bi with q' , tr' , bi' ← ~iright bi tr = step tr' bi'


module Classical where

  private 
    postulate ¬¬-elim : ∀ {l} {A : Set l} → ¬ ¬ A → A

    ¬∀-∃ : ∀ {l l'} → {A : Set l}  {P : A → Set l'} → ¬ (∀ i → P i) → (∃[ i ] ¬ P i)
    ¬∀-∃ ne =  ¬¬-elim λ f → ne (λ i → ¬¬-elim λ g → f (i , g))

    lem : ∀ {l} (A : Set l) → A ⊎ ¬ A
    lem _ = ¬¬-elim (λ f → f (inj₂ (λ a → f (inj₁ a))))

    mutual
      fin-nondet : ∀ {E A l l'} (p : CTree' E A) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {p'} → p [ l ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {p'} → p [ l ]⇒ p' → P p' i
      fin-nondet (p ↑) = fin-nondet↑ p
      fin-nondet (wait B c) = fin-nondet-wait c

      fin-nondet↑ : ∀ {E A l l'} (p : CTree E A ∞) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {p'} → p ↑ [ l ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {p'} → p ↑ [ l ]⇒ p' → P p' i

      fin-nondet↑ {l = l} (now v) down step with lem (l ≡ ⟨ ρ v ⟩)
      ... | inj₁ refl with i , Pp' ← step (⇒-now v) = i , λ {(⇒-now v) → Pp'}
      ... | inj₂ neq =  0 ,  λ {(⇒-now v) →  ⊥-elim (neq refl)}
      fin-nondet↑ {l = ⟨ a ⟩} (later p) down step = 0 ,  λ ()
      fin-nondet↑ {l = τ} (later p) down step with i , Pp ← step ⇒-later = i ,  λ {⇒-later → Pp}
      fin-nondet↑ (p1 ⊕ p2) down step
        with i1 , P1 ← fin-nondet↑ p1 down (λ tr → step (⇒-⊕-l tr))
        with i2 , P2 ← fin-nondet↑ p2 down (λ tr → step (⇒-⊕-r tr))
          = i1 ⊔ i2 ,  λ { (⇒-⊕-l tr) → down (m≤m⊔n i1 i2) (P1 tr) ;
                           (⇒-⊕-r tr) → down (m≤n⊔m i1 i2) (P2 tr)}
      fin-nondet↑ ∅ down step  = 0 , λ ()
      fin-nondet↑ {l = l} (eff {B = B} e c) down step with lem (l ≡ ⟨ ε e ⟩)
      ... | inj₁ (refl) with i , Pp' ← step (⇒-eff e c) = i , λ {(⇒-eff _ _)  → Pp' }
      ... | inj₂ neq = 0 ,  λ {(⇒-eff _ _) → ⊥-elim (neq refl)}

      fin-nondet-wait : ∀ {E A l l' B} (c : B → CTree E A ∞) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {p'} → wait B c [ l ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {p'} → wait B c [ l ]⇒ p' → P p' i
      
      fin-nondet-wait {l = l} {B = B} c down step with lem (Σ[ r ∈ B ] l ≡ ⟨ ι r ⟩)
      ... | inj₁ (r , refl) with i , Pp' ← step (⇒-inp r c) = i , λ {(⇒-inp _ _)  → Pp' }
      ... | inj₂ neq = 0 ,  λ {(⇒-inp r _) → ⊥-elim (neq (r , refl))}


-- indexed bisimilarity ⇒ bisimilarity

  ~i-~ : ∀ {E A j} {p q : CTree' E A} → (∀ i → p ~̂[ i ] q) → (p ~̂ q) {j}
  ~-left (~i-~ {p = p} {q} ibi) {p' = p'} tr = ¬¬-elim  λ ¬left →
    ¬~ileft tr (proj₂ (fin-nondet _ (λ le ¬Pi Pj → ¬Pi (~idown le Pj))
    (λ {q'} tr' → ¬∀-∃ λ trs → ¬left (q' , tr' , ~i-~ trs)  ))) (ibi _) 
  ~-right (~i-~ {p = p} {q} ibi) {q' = q'} tr = ¬¬-elim  λ ¬right →
    ¬~iright tr (proj₂ (fin-nondet _ (λ le ¬Pi Pj → ¬Pi (~idown le Pj))
    (λ {q'} tr' → ¬∀-∃ λ trs → ¬right (q' , tr' , ~i-~ trs)  ))) (ibi _) 

open Classical public
