{-# OPTIONS --sized-types #-}

---------------------------------------------
-- monad and functor laws for choice trees --
---------------------------------------------


module CTree.IndexedBisimilarity.MonadLaws where

open import CTree.IndexedBisimilarity.Definitions public
open import CTree.IndexedBisimilarity.BasicProperties
open import Data.Nat
open import Function using (id; _∘_)

----------------
-- monad laws --
----------------

        
>>=-assoc : ∀{i A B C E} (p : CTree E A ∞)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞} →
                ((p >>= k) >>= l) ~[ i ] (p >>= λ a → k a >>= l)
>>=-assoc {zero} p = ~izero
>>=-assoc (now v) = ~irefl
>>=-assoc {suc i} (later p) = ~ilater (>>=-assoc (force p))
>>=-assoc (p ⊕ q) = ⊕-cong (>>=-assoc p) (>>=-assoc q)
>>=-assoc ∅ = ~irefl
>>=-assoc (eff e c) = ~ieff e (λ r → >>=-assoc (c r))

>>-assoc : ∀{i A B C E} (p : CTree E A ∞)
               {q : CTree E B ∞}{r : CTree E C ∞} →
               (p >> q) >> r ~[ i ] p >> (q >> r)
>>-assoc p = >>=-assoc p


>>=-return : ∀ {E A i} {p : CTree E A ∞}  → (p >>= return) ~[ i ] p
>>=-return {i = zero} = ~izero
>>=-return {p = now v} = ~irefl
>>=-return {i = suc i} {p = later p} = ~ilater >>=-return
>>=-return {p = p ⊕ q} = ⊕-cong >>=-return >>=-return
>>=-return {p = ∅} = ~irefl
>>=-return {p = eff e c} = ~ieff e (λ r → >>=-return)


return->>= : ∀ {E A B} {i} {x : A} {f : A → CTree E B ∞}  → (return x >>= f) ~[ i ] f x
return->>= = ~irefl

------------------
-- functor laws --
------------------


map-id : ∀ {E A i} (p : CTree E A ∞) → map id p ~[ i ] p
map-id _ = >>=-return

map-∘ : ∀ {E A B C i} (p : CTree E A ∞) {f : A → B} {g : B → C}
  → map g (map f p) ~[ i ] map (g ∘ f) p
map-∘ p = >>=-assoc p
