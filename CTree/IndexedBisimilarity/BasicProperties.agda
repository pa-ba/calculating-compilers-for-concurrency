{-# OPTIONS --sized-types #-}


-----------------------------------------------------
-- basic properties of indexed strong bisimilarity --
-----------------------------------------------------


module CTree.IndexedBisimilarity.BasicProperties where

open import CTree.IndexedBisimilarity.Definitions public

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

-- helper function for well-founded recursion
recStep : ∀ {E A l i} {p p' : CTree' E A} → p [ l ]⇒ p' →
  suc (lsuc l i) ≤ suc i ⊎ lsuc l i ≡ suc i × ∃[ a ] p [ ⟨ a ⟩ ]⇒ p'
recStep {l = ⟨ x ⟩} tr = inj₂ (refl , x , tr)
recStep {l = τ} tr = inj₁ ≤-refl

-- helper function for well-founded recursion
recStep⁺ : ∀ {E A l i} {p p' : CTree' E A} →  p [ l ]⇒ p' →
  suc (lsuc l i) ≤ suc i ⊎ lsuc l i ≡ suc i × TransClosure (λ q q' → ∃[ a ] q' [ ⟨ a ⟩ ]⇒ q) p' p
recStep⁺ {l = ⟨ x ⟩} tr = inj₂ (refl , [  (x , tr) ] )
recStep⁺ {l = τ} tr = inj₁ ≤-refl


---------------------------------------------------
-- basic properties of indexed strong bisimilarity 
---------------------------------------------------


~irefl : ∀ {i E A} {p : CTree' E A} → p ~̂[ i ] p
~irefl = prf (<×⇐-wf _)
  where prf : ∀ {i E A} {p : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ~̂[ i ] p
        prf {zero} _ = ~izero
        prf {suc i} (acc rec) =
          ~istep
            (λ trans →  _ , trans , prf (rec _ (recStep trans)))
            (λ trans →  _ , trans , prf (rec _ (recStep trans)))




~isym : ∀ {i E A} {p q : CTree' E A} → p ~̂[ i ] q → q ~̂[ i ] p
~isym = prf (<×⇐-wf _)
  where prf : ∀ {i E A} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ~̂[ i ] q → q ~̂[ i ] p
        prf _ ~izero = ~izero
        prf {i = suc i} {p = p} {q} (acc rec) b = ~istep left right
          where left : ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × q' ~̂[ lsuc l i ] p')
                left trans with q' , trans' , ibi' ← ~iright b trans
                  = q' , trans' , prf (rec _ (recStep trans')) ibi'
                right : ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × q' ~̂[ lsuc l i ] p')
                right trans with q' , trans' , ibi' ← ~ileft b trans
                   = q' , trans' , prf (rec _ (recStep trans)) ibi'


~itrans : ∀ {i E A} {p q r : CTree' E A} → p ~̂[ i ] q → q ~̂[ i ] r → p ~̂[ i ] r
~itrans b1 b2 = prf (<×⇐-wf _) b1 b2
  where prf : ∀ {i E A} {p q r : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ~̂[ i ] q → q ~̂[ i ] r → p ~̂[ i ] r
        prf _ ~izero ~izero = ~izero
        prf {i = suc i} {p = p} {q} {r} (acc rec) b1 b2 = ~istep left right
            where left : ∀ {l p'} → p [ l ]⇒ p' → ∃[ r' ] (r [ l ]⇒ r' × p' ~̂[ lsuc l i ] r')
                  left trans1 with ~ileft b1 trans1
                  ... | q' , trans2 , b1' with ~ileft b2 trans2
                  ... | r' , trans3 , b2' =  r' , trans3 , prf (rec _ (recStep trans1))  b1'  b2'
                  right : ∀ {l r'} → r [ l ]⇒ r' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂[ lsuc l i ] r')
                  right trans3 with ~iright b2 trans3
                  ... | q' , trans2 , b2' with ~iright b1 trans2
                  ... | p' , trans1 , b1' =  p' , trans1 , prf (rec _ (recStep trans1))  b1' b2'

~ilater : ∀ {i E A} {a b : ∞CTree E A ∞} → force a ~[ i ] force b → later a ~[ suc i ] later b
~ilater b = ~istep (λ {⇒-later →  _ , ⇒-later , b }) λ {⇒-later →  _ , ⇒-later , b }

~idown : ∀ {E A i j} {a b : CTree' E A} → j ≤ i → a ~̂[ i ] b → a ~̂[ j ] b
~idown = prf (<×⇐-wf _)
  where prf : ∀ {E A i j} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → j ≤ i → p ~̂[ i ] q → p ~̂[ j ] q
        prf _ z≤n b = ~izero
        prf {j = suc j} {p = p} {q} (acc rec) (s≤s le) b = ~istep left right
          where left : ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂[ lsuc l j ] q')
                left {l} trans with ~ileft b trans
                ... | q' , trans' , b' = q' , trans' , prf (rec _ (recStep trans)) (lsuc-mono l le) b'
                right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂[ lsuc l j ] q')
                right {l} trans with ~iright b trans
                ... | p' , trans' , b' = p' , trans' , prf (rec _ (recStep trans')) (lsuc-mono l le) b'

~isuc : ∀ {E A i} {a b : CTree' E A} → a ~̂[ suc i ] b → a ~̂[ i ] b
~isuc e = ~idown (n≤1+n _) e

~iwait : ∀{E A B i} {c d : B → CTree E A ∞} → (∀ x → c x ~[ i ] d x)
  → wait B c ~̂[ i ] wait B d
~iwait {i = zero} bs = ~izero
~iwait {i = suc i} {c} {d} bs = ~istep left right
  where left : ∀ {l p'} → wait _ c [ l ]⇒ p' → ∃[ q' ] (wait _ d [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')
        left (⇒-inp r c) = d r ↑  , ⇒-inp r d , bs r
        right : ∀ {l q'} → wait _ d [ l ]⇒ q' → ∃[ p' ] (wait _ c [ l ]⇒ p' × p' ~̂[ lsuc l i ] q')
        right (⇒-inp r d) = c r ↑ , ⇒-inp r c , bs r


~iwait' : ∀ {i E A B}  {c d : B → CTree E A ∞}  → wait B c ~̂[ i ] wait B d →
           (∀ r → c r ~[ i ] d r)
~iwait' {zero} b r = ~izero
~iwait' {suc i} {c = c} {d} b r
  with q' , (⇒-inp r d) , b' ← ~ileft b (⇒-inp r c) = b'




~ieff : ∀{E A B i} {c d : B → CTree E A ∞} (e : E B) → (∀ x → c x ~[ i ] d x) → eff e c ~[ i ] eff e d
~ieff {i = zero} e bs = ~izero
~ieff {i = suc i} {c} {d} e bs = ~istep left right
  where left : ∀ {l p'} → eff e c ↑ [ l ]⇒ p' → ∃[ q' ] (eff e d ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')
        left (⇒-eff e c) = wait _ d  , ⇒-eff e d ,  ~iwait bs
        right : ∀ {l q'} → eff e d ↑ [ l ]⇒ q' → ∃[ p' ] (eff e c ↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q')
        right (⇒-eff e d) = wait _ c , ⇒-eff e c , ~iwait bs


⊕-cong : ∀ {E A i} {p1 q1 p2 q2 : CTree E A ∞} → p1 ~[ i ] p2 → q1 ~[ i ] q2
  → p1 ⊕ q1 ~[ i ] p2 ⊕ q2
⊕-cong {i = zero} ~p ~q = ~izero
⊕-cong {i = suc i} {p1} {q1} {p2} {q2} ~p ~q = ~istep left right where
  left : ∀ {l p'} → (p1 ⊕ q1) ↑ [ l ]⇒ p' → ∃[ q' ] (p2 ⊕ q2) ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l tr) with q' , tr' , b' ← ~ileft ~p tr = q' , ⇒-⊕-l tr' , b'
  left (⇒-⊕-r tr) with q' , tr' , b' ← ~ileft ~q tr = q' , ⇒-⊕-r tr' , b'
  right : ∀ {l q'} → (p2 ⊕ q2)↑ [ l ]⇒ q' → ∃[ p' ] (p1 ⊕ q1)↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right (⇒-⊕-l tr) with q' , tr' , b' ← ~iright ~p tr = q' , ⇒-⊕-l tr' , b'
  right (⇒-⊕-r tr) with q' , tr' , b' ← ~iright ~q tr = q' , ⇒-⊕-r tr' , b'

⊕-cong-r : ∀ {E A i} {p q q' : CTree E A ∞} → q ~[ i ] q' → p ⊕ q ~[ i ] p ⊕ q'
⊕-cong-r ~q = ⊕-cong ~irefl ~q


⊕-cong-l : ∀ {E A i} {p q p' : CTree E A ∞} → p ~[ i ] p' → p ⊕ q ~[ i ] p' ⊕ q
⊕-cong-l ~p =  ⊕-cong ~p ~irefl


_~̂⟨_⟩_ : ∀ {E} {A : Set} {i} (x : CTree' E A) →
  ∀ {y : CTree' E A} {z : CTree' E A} → x ~̂[ i ] y → y ~̂[ i ] z → x ~̂[ i ] z
_~̂⟨_⟩_ {_} x r eq =  ~itrans r eq

_~̂⟨⟩_ : ∀ {E} {A : Set} {i} (x : CTree' E A) → ∀ {y : CTree' E A} → x ~̂[ i ] y → x ~̂[ i ] y
_~̂⟨⟩_  x eq = eq

_~⟨_⟩_ : ∀ {E} {A : Set} {i} (x : CTree E A ∞) →
  ∀ {y : CTree E A ∞} {z : CTree E A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
_~⟨_⟩_ {_} x r eq =  ~itrans r eq

_~⟨⟩_ : ∀ {E} {A : Set} {i} (x : CTree E A ∞) → ∀ {y : CTree E A ∞} → x ~[ i ] y → x ~[ i ] y
_~⟨⟩_  x eq = eq



_∎̂ : ∀ {E} {A : Set} {i} (x : CTree' E A) → x ~̂[ i ] x
_∎̂  x = ~irefl

_∎ : ∀ {E} {A : Set} {i} (x : CTree E A ∞) → x ~[ i ] x
_∎  x = ~irefl

infix  3 _∎
infix  3 _∎̂
infixr 1 _~̂⟨_⟩_
infixr 1 _~̂⟨⟩_
infixr 1 _~⟨_⟩_
infixr 1 _~⟨⟩_
