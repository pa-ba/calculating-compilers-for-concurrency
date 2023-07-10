{-# OPTIONS --sized-types #-}

-- Properties for the monadic bind operator >>=

module CTree.IndexedBisimilarity.Bind where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.MonadLaws public
open import CTree.Parallel public
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Function using (id; _∘_)
open import Relation.Nullary
------------------------
-- congruence for >>= --
------------------------


_>>='_ : ∀ {A B E} → CTree' E A → (A → CTree E B ∞) → CTree' E B
wait _ c >>=' f = wait _ (λ r → c r >>= f)
(p ↑) >>=' f = (p >>= f) ↑


>>=-cong-r : ∀ {i E A B}  (a : CTree E A ∞)
            {k l : A → CTree E B ∞} (h : ∀ a → k a ~[ i ] l a) →
            (a >>= k) ~[ i ] (a >>= l)
>>=-cong-r {0} _ _ = ~izero
>>=-cong-r (now v) h =  h v
>>=-cong-r {suc i} (later p) h = ~ilater (>>=-cong-r (force p) λ x → ~idown (≤-step ≤-refl) (h x))
>>=-cong-r (p ⊕ q) h = ⊕-cong (>>=-cong-r p h) (>>=-cong-r q h)
>>=-cong-r ∅ h = ~irefl
>>=-cong-r (eff e c) h = ~ieff e λ r → >>=-cong-r (c r) h


>>='-cong-r : ∀ {i E A B}  (a : CTree' E A)
            {k l : A → CTree E B ∞} (h : ∀ a → k a ~[ i ] l a) →
            (a >>=' k) ~̂[ i ] (a >>=' l)
>>='-cong-r (p ↑) h = >>=-cong-r p h
>>='-cong-r (wait B c) h = ~iwait (λ r → >>=-cong-r (c r) h)

>>=-step : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → CTree E B ∞) →
  (p >>=' k) [ l ]⇒ q → (∃[ v ]  ((p [ ⟨ ρ v ⟩ ]⇒ ∅ ↑) × (k v ↑ [ l ]⇒ q)))
    ⊎ (∃[ l' ] retFree l l' × (∃[ p' ] p [ l' ]⇒ p' × q ≡ p' >>=' k))
>>=-step (now v ↑) k trans = inj₁ ( v , ⇒-now v , trans)
>>=-step (later p ↑) k ⇒-later = inj₂ ( τ , retFreeτ ,  force p ↑ ,  ⇒-later , refl)
>>=-step ((p ⊕ q) ↑) k (⇒-⊕-l trans) with >>=-step (p ↑) k trans
... | inj₁ (v , trans1 , trans2)  = inj₁ (v , ⇒-⊕-l trans1 , trans2)
... | inj₂ (l' , rf , p' , trans' , b) = inj₂ ( l' , rf , p' , ⇒-⊕-l trans' , b)
>>=-step ((p ⊕ q)↑) k (⇒-⊕-r trans) with >>=-step (q ↑) k trans
... | inj₁ (v , trans1 , trans2)  = inj₁ (v , ⇒-⊕-r trans1 , trans2)
... | inj₂ (l' , rf , p' , trans' , b) = inj₂ ( l' , rf , p' , ⇒-⊕-r trans' , b)
>>=-step (eff e c ↑) k (⇒-eff .e _) = inj₂ ( ⟨ ε e ⟩ , retFreeε ,  wait _ c ,  ⇒-eff e c , refl)
>>=-step (wait _ c) k (⇒-inp r _) = inj₂ ( ⟨ ι r ⟩ , retFreeι ,  c r ↑ ,  ⇒-inp r c , refl)

>>=-step1 : ∀ {E A B l v} {p : CTree' E A} {p' : CTree' E A} {q : CTree' E B} (k : A → CTree E B ∞) →
          p [ ⟨ ρ v ⟩ ]⇒ p' → k v ↑ [ l ]⇒ q → (p >>=' k) [ l ]⇒ q
>>=-step1 k (⇒-now _) tr2 = tr2
>>=-step1 k (⇒-⊕-l tr1) tr2 = ⇒-⊕-l (>>=-step1 k tr1 tr2)
>>=-step1 k (⇒-⊕-r tr1) tr2 = ⇒-⊕-r (>>=-step1 k tr1 tr2)

>>=-step2 : ∀ {E A B l l' p'} (p : CTree' E A ) (k : A → CTree E B ∞) →
          retFree l l' → p [ l' ]⇒ p' → p >>=' k [ l ]⇒ p' >>=' k
>>=-step2 (now v ↑) k () (⇒-now .v) 
>>=-step2 (later p ↑) k retFreeτ ⇒-later = ⇒-later
>>=-step2 ((p ⊕ q)↑) k rf (⇒-⊕-l tr)
  with tr' ← >>=-step2 (p ↑) k rf tr =  ⇒-⊕-l tr'
>>=-step2 ((p ⊕ q)↑) k rf (⇒-⊕-r tr)
  with tr' ← >>=-step2 (q ↑) k rf tr =  ⇒-⊕-r tr'
>>=-step2 (eff e c ↑) k retFreeε (⇒-eff .e .c) = ⇒-eff e _
>>=-step2 (wait _ c) k retFreeι (⇒-inp r _) = ⇒-inp r _



>>=-cong-l : ∀ {i E A B}  {p q : CTree' E A} (b : p ~̂[ i ] q)
              {k : A → CTree E B ∞} →
              (p >>=' k) ~̂[ i ] (q >>=' k)
>>=-cong-l {i} = prf i (<×⇐-wf _) where
  prf : ∀ {E A B}  {p q : CTree' E A} i (ac : Acc (×-Lex _≡_ _<_ _⇐_) (i , p)) (b : p ~̂[ i ] q)
          {k : A → CTree E B ∞} → (p >>=' k) ~̂[ i ] (q >>=' k)
  prf zero _ b = ~izero
  prf {p = p} {q} (suc i) (acc rec) b {k} = ~istep left right where
    left : ∀ {l pk'} → p >>=' k [ l ]⇒ pk' → ∃[ qk' ] q >>=' k [ l ]⇒ qk' × pk' ~̂[ lsuc l i ] qk'
    left trans with >>=-step p k trans
    ... | inj₁ (v , trans1 , trans2) with ~ileft b trans1
    ... | q' , trans1' , b' =  _ , >>=-step1 k trans1' trans2 , ~irefl
    left {⟨ a ⟩} trans | inj₂ (l' , rf , p' , trans' , refl) with retFreeAction rf
    ... | a' , refl with ~ileft b trans'
    ... | q' , trans'' , b'' =  _ , >>=-step2 q k rf trans'' ,
        prf (suc i) (rec (suc i , p') (inj₂(refl , _ , trans'))) b''
    left {τ} trans | inj₂ (.τ , retFreeτ , p' , trans' , refl)  with ~ileft b trans'
    ... | q' , trans'' , b'' =  _ , >>=-step2 q k retFreeτ trans'' ,
        ~itrans ~irefl (prf i (rec (i , p') (inj₁ ≤-refl)) b'')


    right : ∀ {l qk'} → q >>=' k [ l ]⇒ qk' → ∃[ pk' ] p >>=' k [ l ]⇒ pk' × pk' ~̂[ lsuc l i ] qk'
    right trans with >>=-step q k trans
    ... | inj₁ (v , trans1 , trans2) with ~iright b trans1
    ... | p' , trans1' , b' =  _ , >>=-step1 k trans1' trans2 , ~irefl
    right {⟨ a ⟩} trans | inj₂ (l' , rf , q' , trans' , refl) with retFreeAction rf
    ... | a' , refl with ~iright b trans'
    ... | p' , trans'' , b'' =  _ , >>=-step2 p k rf trans'' ,
         prf (suc i) (rec (suc i , p') (inj₂ (refl , _ , trans''))) b''
    right {τ} trans | inj₂ (.τ , retFreeτ , q' , trans' , refl)  with ~iright b trans'
    ... | p' , trans'' , b'' =  _ , >>=-step2 p k retFreeτ trans'' ,
        prf i (rec (i , p') (inj₁ ≤-refl)) b''


>>=-cong : ∀ {i E A B}  {p q : CTree' E A} (b : p ~̂[ i ] q)
              {k l : A → CTree E B ∞} →
              (h : ∀ a → k a ~[ i ] l a) →
              (p >>=' k) ~̂[ i ] (q >>=' l)
>>=-cong {q = q} b h = ~itrans (>>=-cong-l b) (>>='-cong-r q h)



>>=-cong-assoc : ∀ {i E A B1 B2 C} (p : CTree E A ∞) {f1 : A → CTree E B1 ∞} {f2 : A → CTree E B2 ∞}
  {g1 : B1 → CTree E C ∞} {g2 : B2 → CTree E C ∞} → (∀ x → (f1 x >>= g1) ~[ i ] (f2 x >>= g2))
    → ((p >>= f1) >>= g1) ~[ i ] ((p >>= f2) >>= g2)
>>=-cong-assoc p eq = ~itrans (>>=-assoc p)
                        (~itrans (>>=-cong-r p eq)
                          (~isym (>>=-assoc p)) )


>>='-assoc : ∀{i A B C E} (p : CTree' E A)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞} →
                ((p >>=' k) >>=' l) ~̂[ i ] (p >>=' λ a → k a >>= l)
>>='-assoc (p ↑) = >>=-assoc p
>>='-assoc (wait B c) = ~iwait (λ r → >>=-assoc (c r))



------------------------
-- congruence for map --
------------------------


map' : ∀ {A B E} → (A → B) → CTree' E A → CTree' E B
map' f p = p >>=' (λ x → return (f x))


map'-id : ∀ {E A i} (p : CTree' E A) → map' id p ~̂[ i ] p
map'-id (p ↑) = map-id p
map'-id (wait B c) = ~iwait (λ r → map-id (c r))

map'-∘ : ∀ {E A B C i} (p : CTree' E A) {f : A → B} {g : B → C}
  → map' g (map' f p) ~̂[ i ] map' (g ∘ f) p
map'-∘ (p ↑) = map-∘ p
map'-∘ (wait B c) = ~iwait (λ r → map-∘(c r))

map-cong : ∀ {i E A B}  {p q : CTree' E A} (b : p ~̂[ i ] q)
                {f : A → B} → map' f p ~̂[ i ] map' f q
map-cong b = >>=-cong-l b



map->>= : ∀ {E A B C i} (p : CTree E A ∞)
                {k : A → B}{l : B → CTree E C ∞} →
                ((map k p) >>= l) ~[ i ] (p >>= λ a → l (k a))
map->>= p {k} {l} = ~itrans (>>=-assoc p) (>>=-cong-r p (λ r → return->>= {f = l}))

-----------
-- never --
-----------

never->>= : ∀ {i A B E} {f : A → CTree E B ∞} → (never >>= f) ~[ i ] never
never->>= {zero} = ~izero
never->>= {suc i} {f = f} = ~istep left right where
  left : ∀ {l p'} → later (∞never ∞>>= f) ↑ [ l ]⇒ p' → ∃[ q' ] never ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left ⇒-later = _ ,  ⇒-later , never->>= {i}
  right : ∀ {l q'} → never ↑ [ l ]⇒ q' → ∃[ p' ] later (∞never ∞>>= f) ↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right ⇒-later = _ , ⇒-later , never->>= {i}


map-step : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → B) →
  (map' k p) [ l ]⇒ q → (∃[ v ]  ((p [ ⟨ ρ v ⟩ ]⇒ ∅ ↑) × l ≡ ⟨ ρ (k v) ⟩ ))
    ⊎ (∃[ l' ] retFree l l' × (∃[ p' ] p [ l' ]⇒ p' × q ≡ map' k p'))
map-step p k tr with >>=-step p (λ x → return (k x)) tr
... | inj₁ (v , tr1 , ⇒-now .(k v)) = inj₁ ( v , tr1 , refl)
... | inj₂ (l' , rf , p' , tr' , refl) = inj₂ (l' , rf , p' , tr' , refl)

map-step1 : ∀ {E A B v} {p : CTree' E A} {p' : CTree' E A} (k : A → B) →
          p [ ⟨ ρ v ⟩ ]⇒ p' → (map' k p) [ ⟨ ρ (k v)⟩ ]⇒ ∅ ↑
map-step1 k tr = >>=-step1 (λ x → return (k x)) tr (⇒-now _)

map-step2 : ∀ {E A B l l' p'} (p : CTree' E A ) (k : A → B) →
          retFree l l' → p [ l' ]⇒ p' → map' k p [ l ]⇒ map' k p'
map-step2 p k rf tr = >>=-step2 p (λ x → return (k x)) rf tr

map-step-lmap : ∀ {E A B l p'} (p : CTree' E A ) (k : A → B) →
          p [ l ]⇒ p' → map' k p [ lmap k l ]⇒ map' k p'
map-step-lmap {l = ⟨ ε x ⟩} p k tr = map-step2 p k retFreeε tr
map-step-lmap {l = ⟨ ι x ⟩} p k tr = map-step2 p k retFreeι tr
map-step-lmap {l = ⟨ ρ x ⟩} p k tr rewrite ⇒-ρ-∅ tr = map-step1 k tr
map-step-lmap {l = τ} p k tr = map-step2 p k retFreeτ tr



map-step' : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → B) (k' : B → A) (eq : ∀ v → k' (k v) ≡ v) →
  (map' k p) [ l ]⇒ q → ((∃[ p' ] p [ lmap k' l ]⇒ p' × q ≡ map' k p'))
map-step' p k k' eq tr with map-step p k tr
... | inj₁ (v , tr' , refl) rewrite eq v rewrite ⇒-ρ-∅ tr =  ∅ ↑ , tr' , refl
... | inj₂ (l' , rf , p' , tr' , refl) rewrite retFree-lmap k' rf = p' , tr' , refl 
