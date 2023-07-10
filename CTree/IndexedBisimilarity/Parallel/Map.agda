{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel.Map where

open import CTree.IndexedBisimilarity.BasicProperties
open import CTree.IndexedBisimilarity.Bind
open import CTree.IndexedBisimilarity.Interp
open import CTree.IndexedBisimilarity.Parallel.Congruence
open import CTree.Parallel
open import Data.Nat
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Function using (id; _∘_)

------------------------------
-- map distributes over par --
------------------------------

∥-map : ∀ {i A A' B B' E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
  → map (map× f g)  (p ∥ q) ~[ i ] map f p ∥ map g q
∥-map p q = ⊕-cong (⊕-cong (⦉-map p q) (⦊-map p q)) (⋈-map p q) where

  ⦉-map : ∀ {i A A' B B' E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⦉ q) ~[ i ] map f p ⦉ map g q
  ⦉-map (now v) q = ~irefl
  ⦉-map {zero} (later p) q = ~izero
  ⦉-map {suc i} (later p) q = ~ilater (∥-map (force p) q)
  ⦉-map (p1 ⊕ p2) q = ⊕-cong (⦉-map p1 q) (⦉-map p2 q)
  ⦉-map ∅ q = ~irefl
  ⦉-map (eff e c) q = ~ieff e (λ r → ∥-map (c r) q)

  ⦊-map : ∀ {i A A' B B' E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⦊ q) ~[ i ] map f p ⦊ map g q
  ⦊-map p (now v) = ~irefl
  ⦊-map {zero} p (later q) = ~izero
  ⦊-map {suc i} p (later q) = ~ilater (∥-map p (force q))
  ⦊-map p (q1 ⊕ q2) = ⊕-cong (⦊-map p q1) (⦊-map p q2)
  ⦊-map p ∅ = ~irefl
  ⦊-map p (eff e c) = ~ieff e (λ r → ∥-map p (c r))

  ⋈-map : ∀ {i A A' B B' E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⋈ q) ~[ i ] map f p ⋈ map g q
  ⋈-map (now v) (now v₁) = ~irefl
  ⋈-map (now v) (later p) = ~irefl
  ⋈-map (now v) (q1 ⊕ q2) = ⊕-cong (⋈-map (now v) q1) (⋈-map (now v) q2)
  ⋈-map (now v) ∅ = ~irefl
  ⋈-map (now v) (eff e c) = ~irefl
  ⋈-map (later p) (now v) = ~irefl
  ⋈-map (later p) (later p₁) = ~irefl
  ⋈-map (later p) (q1 ⊕ q2) = ⊕-cong (⋈-map (later p) q1) (⋈-map (later p) q2)
  ⋈-map (later p) ∅ = ~irefl
  ⋈-map (later p) (eff e c) = ~irefl
  ⋈-map (p1 ⊕ p2) q =  ⊕-cong (⋈-map p1 q) (⋈-map p2 q)
  ⋈-map ∅ (now v) = ~irefl
  ⋈-map ∅ (later p) = ~irefl
  ⋈-map ∅ (q1 ⊕ q2) = ⊕-cong (⋈-map ∅ q1) (⋈-map ∅ q2)
  ⋈-map ∅ ∅ = ~irefl
  ⋈-map ∅ (eff e c) = ~irefl
  ⋈-map (eff e c) (now v) = ~irefl
  ⋈-map (eff e c) (later p) = ~irefl
  ⋈-map p@(eff e c) (q1 ⊕ q2) = ⊕-cong (⋈-map p q1) (⋈-map p q2)
  ⋈-map (eff e c) ∅ = ~irefl
  ⋈-map {zero} _ _ = ~izero
  ⋈-map {suc i} (eff e1 c1) (eff e2 c2) =
    ~itrans (>>=-assoc (e1 ⇄ e2)) (>>=-cong-r (e1 ⇄ e2) λ (r1 , r2) → ∥-map (c1 r1) (c2 r2))




------------------------------------
-- Corresponding properties for ∥⃗ --
------------------------------------

∥⃗-map-r : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : B → C} 
  → map f (p ∥⃗ q) ~[ i ] p ∥⃗ (map f q)
∥⃗-map-r p q {f} = 
  map f (map proj₂ (p ∥ q))
    ~⟨ map-∘ (p ∥ q) ⟩
  map (λ (x , y) → proj₂ (x , f y)) (p ∥ q)
    ~⟨ ~isym (map-∘ (p ∥ q)) ⟩
  map proj₂ (map (λ (x , y) → (x , f y)) (p ∥ q))
    ~⟨ map-cong (∥-map p q) ⟩
  map id p ∥⃗ map f q
    ~⟨ ∥⃗-cong-l (map-id p) ⟩
  (p ∥⃗ map f q)
  ∎

∥⃗-map-r' : ∀ {i A B C D E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : B → C} {g : C → CTree E D ∞}
  → ((p ∥⃗ q) >>= (λ v → g (f v))) ~[ i ] ((p ∥⃗ (map f q)) >>= g)
∥⃗-map-r' p q {f} {g} =
  (((p ∥ q) >>= λ x → return (proj₂ x)) >>= (λ v → g (f v)))
  ~⟨ >>=-assoc (p ∥ q) ⟩
  ((p ∥ q) >>= (λ x → return (proj₂ x) >>= (λ v → g (f v))))
  ~⟨⟩
  ((p ∥ q) >>= (λ x → g (f (proj₂ x))))
  ~⟨⟩
  ((p ∥ q) >>= (λ x → return (f (proj₂ x)) >>= g))
  ~⟨ ~isym (>>=-assoc (p ∥ q)) ⟩
  ((p ∥ q) >>= (λ x → return (f (proj₂ x))) >>= g)
  ~⟨ >>=-cong-l (~isym (map-∘ (p ∥ q))) ⟩
  ((map f (p ∥⃗ q)) >>= g)
  ~⟨ >>=-cong-l (∥⃗-map-r p q) ⟩
  ((p ∥⃗ map f q) >>= g)
  ∎

∥⃗-map-l : ∀ {i A A' B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'}
  → p ∥⃗ q ~[ i ]  map f p ∥⃗ q
∥⃗-map-l p q {f} =
  map proj₂ (p ∥ q)
  ~⟨⟩
  map (λ (x , y) → proj₂ (f x , y)) (p ∥ q)
  ~⟨ ~isym (map-∘ (p ∥ q)) ⟩
  map proj₂ (map (map× f id) (p ∥ q))
  ~⟨ map-cong (∥-map p q) ⟩
  map f p ∥⃗ map id q
  ~⟨ ∥⃗-cong-r (map-id q) ⟩
  map f p ∥⃗ q
  ∎
