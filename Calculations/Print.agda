{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for the simple arithmetic language with concurrency and
-- a print effect.
------------------------------------------------------------------------

module Calculations.Print where

open import CCTree
import CTree as CT

open import Data.Nat
open import Data.List hiding (map)
open import Data.Unit


-------------
-- Effects --
-------------


data PrintEff : Set → Set where
  PrintInt : ℕ → PrintEff ⊤


instance
  pr : Concurrent PrintEff
  _⇄_ {{pr}} _ _ = CT.∅

print : ∀ {i} → ℕ → CCTree PrintEff ⊤ i
print n = eff (PrintInt n) return

---------------------
-- Source language --
---------------------

data Expr : Set where
  Val   : ℕ → Expr
  Add   : Expr → Expr → Expr
  Print : Expr → Expr
  Fork  : Expr → Expr

eval : ∀ {i} → Expr → CCTree PrintEff ℕ i
eval (Val x)   = return x
eval (Add x y) = do n ← eval x; m ← eval y; return (n + m)
eval (Print x) = do n ← eval x; print n; return n
eval (Fork x)  = eval x ∥⃗ return 0

---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH  : ℕ → Code → Code
  ADD   : Code → Code
  PRINT : Code → Code
  FORK  : Code → Code → Code
  HALT  : Code

Stack : Set
Stack = List ℕ

exec : ∀ {i} → Code → Stack → CCTree PrintEff Stack i
exec (PUSH n c)   s          = exec c (n ∷ s)
exec (ADD c)     (n ∷ m ∷ s) = exec c ((m + n) ∷ s)
exec (PRINT c)   (n ∷ s)     = print n >> exec c (n ∷ s)
exec (FORK c' c) s           = (exec c' [] ∥⃗ exec c (0 ∷ s))
exec HALT        s           = return s
exec _           _           = ∅

--------------
-- Compiler --
--------------


comp : Expr → Code → Code
comp (Val n)   c = PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (Print x) c = comp x (PRINT c)
comp (Fork x)  c = FORK (comp x HALT) c

-----------------
-- Calculation --
-----------------

-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.

spec : ∀ i x {s c} →
  (do v ← eval x; exec c (v ∷ s))  ~[ i ] (exec (comp x c) s)
spec zero _ =  ~izero
spec i (Val n) {s} {c} =
  (do v ← eval (Val n); exec c (v ∷ s))
  ~⟨ return->>= ⟩
  exec c (n ∷ s)
  ~⟨⟩
  (exec (PUSH n c) s)
  ∎

spec i (Add x y) {s} {c} =
  (do v ← eval (Add x y); exec c (v ∷ s))
 ~⟨⟩
  (do v <- (do n ← eval x; m ← eval y; return (n + m)); exec c (v ∷ s))
 ~⟨ >>=-assoc' _ (\ n → >>=-assoc' _ \ m → return->>=) ⟩
  (do n ← eval x; m ← eval y; exec c ((n + m) ∷ s))
 ~⟨⟩
  (do n ← eval x; m ← eval y; exec (ADD c) (m ∷ n ∷ s))
 ~⟨  >>=-cong-r (eval x) (\ n' → spec i  y)  ⟩
  (do n ← eval x; exec (comp y (ADD c)) (n ∷ s))
 ~⟨ spec i x ⟩
    exec (comp x (comp y (ADD c))) s
 ∎

spec i (Print x) {s} {c} =
  (do v ← eval (Print x); exec c (v ∷ s))
 ~⟨⟩
  (do v ← (do n ← eval x; print n; return n); exec c (v ∷ s))
 ~⟨ (>>=-assoc' _ λ n → >>-assoc' _ return->>=) ⟩
  (do n ← eval x; print n; exec c (n ∷ s))
 ~⟨⟩
  (do n ← eval x; exec (PRINT c) (n ∷ s))
 ~⟨ spec i x ⟩
  exec (comp x (PRINT c)) s
 ∎

  
spec i (Fork x) {s} {c} =
  (do v ← eval x ∥⃗ return 0; exec c (v ∷ s))
 ~⟨ ∥⃗->>= ⟩
  (eval x ∥⃗ (return 0 >>= λ v → exec c (v ∷ s)))
 ~⟨ ∥⃗-cong-r return->>= ⟩
  (eval x ∥⃗ exec c (0 ∷ s))
 ~⟨ ∥⃗-map-l (eval x) _ ⟩
  ((eval x >>= λ v → exec HALT [ v ]) ∥⃗ exec c (0 ∷ s))
 ~⟨  ∥⃗-cong-l (spec i x) ⟩
  ((exec (comp x HALT) []) ∥⃗ exec c (0 ∷ s))
 ~⟨⟩
  (exec (FORK (comp x HALT) c) s)
 ∎

-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).

spec' : ∀ s c x →
  (do v ← eval x; exec c (v ∷ s))  ~ exec (comp x c) s
spec' s c x =  ~i-~ (λ n → spec n x)



------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT

specCompile : ∀ s x →
  (do v ← eval x; return (v ∷ s))  ~ exec (compile x) s
specCompile s x =  spec' s HALT x
