{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CCTree.IndexedBisimilarity where
open import CCTree.Definitions public
import CTree.Bisimilarity as CT
open import Data.Product hiding (map)
open import Size public
open import Data.Unit
import CTree as CT
open import Data.Nat
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Relation.Binary.PropositionalEquality

---------------------------------------------
-- Definition of step-indexed bisimilarity --
---------------------------------------------

variable
  i : ℕ
  A : Set
  B : Set
  A' : Set
  B' : Set
  C : Set
  S : Set
  E : Set → Set
  F : Set → Set



infix 3 _~[_]_
record _~[_]_ {{_ : Concurrent E}} (p : CCTree E A ∞) (i : ℕ) (q : CCTree E A ∞) : Set₁ where
  constructor ~imk
  field
    ~iapp :  ∀ {R} (k : A → CTree E R ∞) → ⟦ p ⟧ k CT.~[ i ] ⟦ q ⟧ k

open _~[_]_ public

--------------------------------
-- Definition of bisimilarity --
--------------------------------

infix 3 _~_
record _~_  {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E A ∞) : Set₁ where
  constructor ~mk
  field
    ~app :  ∀ {R} (k : A → CTree E R ∞) → ⟦ p ⟧ k CT.~ ⟦ q ⟧ k

open _~_ public

~-~i : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} → (p ~ q) → p ~[ i ] q
~-~i (~mk eq) = ~imk λ k → CT.~-~i (eq k)

~i-~ : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} → (∀ i → p ~[ i ] q) → p ~ q
~i-~ eqi = ~mk λ k → CT.~i-~ λ i → ~iapp (eqi i) k

-----------------------
-- basice properties --
-----------------------

~izero : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ 0 ] q
~izero = ~imk λ k → CT.~izero

~irefl : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞} → p ~[ i ] p
~irefl = ~imk (λ k → CT.~irefl)

~isym : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ i ] q → q ~[ i ] p
~isym (~imk b) = ~imk λ k → CT.~isym (b k)

~itrans : ∀ {{_ : Concurrent E}} {p q r : CCTree E A ∞} → p ~[ i ] q → q ~[ i ] r → p ~[ i ] r
~itrans (~imk b1) (~imk b2) = ~imk λ k → CT.~itrans (b1 k) (b2 k)


------------------------
-- calculation syntax --
------------------------

_~⟨_⟩_ : ∀ {{_ : Concurrent E}} (x : CCTree E A ∞) →
  ∀ {y : CCTree E A ∞} {z : CCTree E A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
_~⟨_⟩_ {_} x r eq =  ~itrans r eq

_~⟨⟩_ : ∀ {{_ : Concurrent E}} (x : CCTree E A ∞) → ∀ {y : CCTree E A ∞} → x ~[ i ] y → x ~[ i ] y
_~⟨⟩_  x eq = eq


_∎ : ∀ {{_ : Concurrent E}} (x : CCTree E A ∞) → x ~[ i ] x
_∎  x = ~irefl

infix  3 _∎
infixr 1 _~⟨_⟩_
infixr 1 _~⟨⟩_


-----------------
-- congruences --
-----------------

>>=-cong : ∀ {{_ : Concurrent E}}  {p q : CCTree E A ∞} (b : p ~[ i ] q)
            {k l : A → CCTree E B ∞} →
            (h : ∀ a → k a ~[ i ] l a) →
            (p >>= k) ~[ i ] (q >>= l)
>>=-cong {q = q} b {k} {l} h = ~imk (λ k'  → CT.~itrans (~iapp b (λ r → ⟦ k r ⟧ k')) (~icong q λ x → ~iapp (h x) k'))

>>=-cong-r : ∀ {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : A → CCTree E B ∞} (h : ∀ a → k a ~[ i ] l a) →
          (a >>= k) ~[ i ] (a >>= l)
>>=-cong-r a h = >>=-cong ~irefl h

>>-cong-r : ∀ {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : CCTree E B ∞} (h : k ~[ i ] l) →
          (a >> k) ~[ i ] (a >> l)
>>-cong-r a h = >>=-cong-r a (λ _ → h)


>>=-cong-l : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} (b : p ~[ i ] q)
             {k : A → CCTree E B ∞} →
             (p >>= k) ~[ i ] (q >>= k)
>>=-cong-l b = >>=-cong b (λ _ → ~irefl)

map-cong : ∀ {{_ : Concurrent E}}  {p q : CCTree E A ∞} (b : p ~[ i ] q)
                {f : A → B} → map f p ~[ i ] map f q
map-cong b = >>=-cong-l b


~ilater : ∀ {{_ : Concurrent E}} {a b : ∞CCTree E A ∞} → force a ~[ i ] force b → later a ~[ suc i ] later b
~ilater (~imk b) = ~imk λ k → CT.~ilater (b k)


⊕-cong : ∀ {{_ : Concurrent E}} {p1 q1 p2 q2 : CCTree E A ∞} → p1 ~[ i ] p2 → q1 ~[ i ] q2
  → p1 ⊕ q1 ~[ i ] p2 ⊕ q2
⊕-cong (~imk b1) (~imk b2) = ~imk λ k → CT.⊕-cong (b1 k) (b2 k)

⊕-cong-r : ∀ {{_ : Concurrent E}} {p q q' : CCTree E A ∞} → q ~[ i ] q' → p ⊕ q ~[ i ] p ⊕ q'
⊕-cong-r ~q = ⊕-cong ~irefl ~q


⊕-cong-l : ∀ {{_ : Concurrent E}} {p q p' : CCTree E A ∞} → p ~[ i ] p' → p ⊕ q ~[ i ] p' ⊕ q
⊕-cong-l ~p =  ⊕-cong ~p ~irefl


--------------------------
-- properties about >>= --
--------------------------

never->>= : ∀ {{_ : Concurrent E}} {f : A → CCTree E B ∞} → (never >>= f) ~[ i ] never
never->>= {i = 0} = ~izero
never->>= {i = suc i} {f = f} = ~imk λ k → CT.~ilater (~iapp (never->>= {f = f}) k)

>>=-later : ∀ {{_ : Concurrent E}} {p : ∞CCTree E A ∞} {f : A → CCTree E B ∞}
  → (later p >>= f) ~[ i ] later (p ∞>>= f)
>>=-later {i = zero} = ~izero
>>=-later {i = suc i} {p = p} {f} = ~imk λ k → CT.~ilater CT.~irefl


----------------
-- monad laws --
----------------

>>=-return : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞}  → (p >>= return) ~[ i ] p
>>=-return = ~imk (λ k → CT.~irefl)

return->>= : ∀ {{_ : Concurrent E}} {i} {x : A} {f : A → CCTree E B ∞}  → (return x >>= f) ~[ i ] f x
return->>= = ~imk (λ k → CT.~irefl)

>>=-assoc : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞} →
                ((p >>= k) >>= l) ~[ i ] (p >>= λ a → k a >>= l)
>>=-assoc p {k} {l} = ~imk λ k → CT.~irefl


>>=-assoc' : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞}{f : A → CCTree E C ∞} →
                (∀ a → k a >>= l ~[ i ] f a) →
                ((p >>= k) >>= l) ~[ i ] (p >>= f)
>>=-assoc' p b = ~itrans (>>=-assoc p) (>>=-cong-r p b)

>>-assoc' : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : CCTree E B ∞}{l : B → CCTree E C ∞}{f : CCTree E C ∞} →
                (k >>= l ~[ i ] f) →
                ((p >> k) >>= l) ~[ i ] (p >> f)
>>-assoc' p b = ~itrans (>>=-assoc p) (>>-cong-r p b)


>>-assoc : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞)
             {q : CCTree E B ∞}{r : CCTree E C ∞} →
             (p >> q) >> r ~[ i ] p >> (q >> r)
>>-assoc p = >>=-assoc p

map->>= : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → B}{l : B → CCTree E C ∞} →
                ((map k p) >>= l) ~[ i ] (p >>= λ a → l (k a))
map->>= p {k} {l} = ~itrans (>>=-assoc p) (>>=-cong-r p (λ r → return->>=))


--------------------------
-- non-determinism laws --
--------------------------


⊕-unit-l : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞} → ∅ ⊕ p ~[ i ] p
⊕-unit-l = ~imk λ k → CT.⊕-unit-l
 
⊕-assoc : ∀ {{_ : Concurrent E}} {p q r : CCTree E A ∞} → (p ⊕ q) ⊕ r ~[ i ] p ⊕ (q ⊕ r)
⊕-assoc = ~imk λ k → CT.⊕-assoc

⊕-idem : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ p ~[ i ] p
⊕-idem = ~imk λ k → CT.⊕-idem

⊕-comm : ∀ {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ⊕ q ~[ i ] q ⊕ p
⊕-comm = ~imk λ k → CT.⊕-comm

⊕-unit-r : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ ∅ ~[ i ] p
⊕-unit-r = ~imk λ k → CT.⊕-unit-r

⊕-distr : ∀ {{_ : Concurrent E}} (p q : CCTree E A ∞) {f : A → CCTree E B ∞}
  → (p ⊕ q) >>= f ~[ i ] (p >>= f) ⊕ (q >>= f)
⊕-distr p q = ~imk λ k → CT.~irefl

∅->>= :  ∀ {{_ : Concurrent E}} {f : A → CCTree E B ∞} → ∅ >>= f ~[ i ] ∅
∅->>= = ~imk λ k → CT.~irefl

-------------------
-- parallel laws --
-------------------

return-∥⃗ : ∀ {{_ : Concurrent E}} {v : A} {p : CCTree E B ∞} 
  → return v ∥⃗ p ~[ i ] p
return-∥⃗ = ~imk λ k → CT.return-∥⃗


∥⃗->>= : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞} {q : CCTree E B ∞} {f : B → CCTree E C ∞}
  → (p ∥⃗ q) >>= f ~[ i ] p ∥⃗ (q >>= f)
∥⃗->>= {q = q} {f} = ~imk λ k → CT.~irefl


∥⃗-cong : ∀ {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q q' : CCTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥⃗ q ~[ i ] p' ∥⃗ q'
∥⃗-cong (~imk b1) (~imk b2) = ~imk λ k → CT.∥⃗-cong (b1 (CT.now)) (b2 k)

∥⃗-cong-l : ∀ {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q : CCTree E B ∞}
  → p ~[ i ] p' → p ∥⃗ q ~[ i ] p' ∥⃗  q
∥⃗-cong-l b = ∥⃗-cong b ~irefl

∥⃗-cong-r : ∀ {{_ : Concurrent E}} {p : CCTree E A ∞}{q q' : CCTree E B ∞}
  → q ~[ i ] q' → p ∥⃗ q ~[ i ] p ∥⃗ q'
∥⃗-cong-r b = ∥⃗-cong ~irefl b

~icong' : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) {k : A → CTree E B ∞} {k' : A → CTree E C ∞}
  (b : ∀ x → k x CT.>> CT.now tt CT.~[ i ] k' x CT.>> CT.now tt) → ⟦ p ⟧ k CT.>> CT.now tt CT.~[ i ] ⟦ p ⟧ k' CT.>> CT.now tt
~icong' p b = CT.~itrans (~icong-map p {f = λ _ → tt}) (CT.~itrans (~icong p b) (CT.~isym (~icong-map p {f = λ _ → tt})))


~icont : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) (f : A → B) →
         ⟦ p ⟧ CT.now  CT.>> CT.now tt CT.~[ i ] (⟦ p ⟧ (λ r → CT.now (f r))) CT.>> CT.now tt
~icont p f = CT.~itrans (~icong-map p) (CT.~isym (~icong-map p))

∥⃗-map-l : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → C}
  → p ∥⃗ q ~[ i ]  map f p ∥⃗ q
∥⃗-map-l p q {f} = ~imk λ k → CT.~itrans (CT.~itrans (CT.∥⃗-map-l (⟦ p ⟧ CT.now) (⟦ q ⟧ k) {f = λ x → tt})
  (CT.∥⃗-cong-l  (~icont p f ))) (CT.~isym ( CT.∥⃗-map-l (⟦ p ⟧ (λ r → CT.now (f r))) (⟦ q ⟧ k) {f = λ x → tt}))  

∥⃗-map : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → A'} {g : B → B'}
  → map g (p ∥⃗ q) ~[ i ]  map f p ∥⃗ map g q
∥⃗-map p q  = ~itrans (∥⃗->>= {p = p} {q = q}) (∥⃗-map-l p _)

∥⃗-assoc : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] p ∥⃗ (q ∥⃗ r)
∥⃗-assoc p q r = ~imk λ k → CT.∥⃗-assoc (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.now) (⟦ r ⟧ k)

∥⃗-comm : ∀ {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] (q ∥⃗ p) ∥⃗ r
∥⃗-comm p q r = ~imk λ k → CT.∥⃗-comm (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.now) (⟦ r ⟧ k)


------------
-- interp --
------------


interpSt-cong : ∀ {{_ : Concurrent E}} {{_ : Concurrent F}} {p q : CCTree E A ∞}
  {st : S} (f : ∀ {B} → S → E B → CCTree F (B × S) ∞)
  → p ~[ i ] q → interpSt st f p ~[ i ] interpSt st f q
interpSt-cong f (~imk b) = ~imk λ k → CT.>>=-cong-l (CT.interpSt-cong (b CT.now))

interpSt-map : ∀ {{_ : Concurrent E}} {{_ : Concurrent F}} {p : CCTree E A ∞}
  {st : S} (f : ∀ {B} → S → E B → CCTree F (B × S) ∞)
  (g : A → B) → map g (interpSt st f p) ~[ i ] interpSt st f (map g p)
interpSt-map {p = p}{st} f g = ~imk λ k → CT.~itrans
  (CT.~isym ((CT.map->>= (CT.interpSt st _ (⟦ p ⟧ CT.now)))  {k = g} {l = k}))
  (CT.>>=-cong-l {p = CT.map g (CT.interpSt st _ (⟦ p ⟧ CT.now))↑} {q = CT.interpSt st _ (⟦ p ⟧ (λ r → CT.now (g r)))↑}
  ( CT.~itrans (CT.interpSt-map (⟦ p ⟧ CT.now) g) ((CT.interpSt-cong (~icong-map p)))) {k = k})
