This repository contains the supplementary material for the paper
*Calculating Compilers for Concurrency*. The material includes Agda
formalisations of all calculations in the paper along with the all the
required background theory, i.e. definitions and laws for (codensity)
choice trees.

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. All source files in this directory
have been typechecked using version 2.6.3 of Agda and version 1.7.2 of
the Agda standard library.

# Files

## Choice Trees

[CTree.agda](CTree.agda): This is the top-level module containing all
definitions and properties concerning choice trees:

- [Definitions.agda](CTree/Definitions.agda): Definition of
  choice trees and some basic operations on them.
- [Parallel.agda](CTree/Parallel.agda): Definition of the
  parallel composition operators and concurrent effect handlers.
- [Transitions.agda](CTree/Transitions.agda): Definition of the
  labelled transition system semantics of choice trees.
- [Bisimilarity.agda](CTree/Bisimilarity.agda): Definition of
  the bisimilarity relation and its properties
- [IndexedBisimilarity.agda](CTree/IndexedBisimilarity.agda): Definition of
  the step-indexed bisimilarity relation and its properties. This
  includes all the laws mentioned in the paper. These laws are proved
  in various submodules:
  * [Definitions.agda](CTree/IndexedBisimilarity/Definitions.agda):
    Defines the step-indexed bisimilarity relation.
  * [BasicProperties.agda](CTree/IndexedBisimilarity/BasicProperties.agda):
    Proves that indexed bisimilarity is an equivalence relation and a
    congruence for the constructors of the choice tree type.
  * [Bind.agda](CTree/IndexedBisimilarity/BasicProperties.agda):
    Proves congruence law for `>>=`.
  * [MonadLaws.agda](CTree/IndexedBisimilarity/MonadLaws.agda):
    Proves the monad laws.
  * [Interp.agda](CTree/IndexedBisimilarity/Interp.agda): Proves
    proves congruence laws for `interp` and `interpSt` along with the
    `interpSt`-`fmap` laws.
  * [NonDeterminism.agda](CTree/IndexedBisimilarity/NonDeterminism.agda):
    Proves that the congruence law for non-deterministic choice and
    that the non-deterministic fragment forms an idempotent,
    commutative monoid
  * [Parallel.agda](CTree/IndexedBisimilarity/Parallel.agda): Proves
    the laws for parallel composition operators.

## Codensity Choice Trees

[CCTree.agda](CCTree.agda): This is the top-level module containing all
definitions and properties concerning codensity choice trees:

- [Definitions.agda](CCTree/Definitions.agda): Definition of codensity
  choice trees and all operations on them.
- [IndexedBisimilarity.agda](CCTree/IndexedBisimilarity.agda):
  Definition of both the bisimilarity and the step-indexed
  bisimilarity relation and their properties. This includes all the
  laws mentioned in the paper.

## Compiler calculations from the paper

- [Calculations/Print.agda](Calculations/Print.agda): Simple arithmetic language with fork and
  print (section 6).
- [Calculations/Lambda.agda](Calculations/Lambda.agda): Concurrent call-by-value lambda calculus
  with channel-based communication (section 8).

## Termination arguments

In some cases, Agda's termination checker rejects the definition of
the virtual machine `exec`. In these cases, the termination checker is
disabled for `exec` (using the `TERMINATING` pragma) and termination
is proved manually in the following modules:

- [Calculations/Terminating/Lambda.agda](Calculations/Terminating/Lambda.agda)

# Agda formalisation vs. paper proofs

In the paper, we use an idealised Haskell-like syntax for all
definitions. Here we outline how this idealised syntax is translated
into Agda.

## Identifier names

The paper uses Haskell conventions for identifier names, which are
different in Agda. For examples, constructors must start with a upper
case letter in Haskell, whereas constructors typically start with a
lower case letter in Agda. As a consequence the constructors of the
`CTree` type are named slightly differently in the Agda code (see
below). Similarly, while we use `fmap` for the functor map in the
paper, we use `map` in the Agda code.

## Sized coinductive types

In the paper, we use the `codata` syntax to distinguish coinductively
defined data types from inductive data types. In particular, we use
this for the `CTree` type:

```haskell
data CTree e a where
   Now  :: a -> CTree e a
   (⊕) :: CTree e a -> CTree e a -> CTree e a
   Zero :: CTree e a
   Eff  :: e b -> (b -> CTree e a) -> CTree e a
   Step :: CTreeInf e a -> CTree e a

codata CTreeInf e a = Delay (CTree e a)
```

In Agda we use coinductive record types to represent coinductive data
types. Moreover, we use sized types to help the termination checker to
recognise productive corecursive function definitions. Therefore, the
`CTree` type has an additional parameter of type `Size`:

```agda
mutual
  data CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    now  : (v : A) → CTree E A i
    _⊕_  : (p q : CTree E A i) → CTree E A i
    ∅    : CTree E A i
    eff  : ∀ {B} → (e : E B) → (c : B → CTree E A i) → CTree E A i
    later : (p : ∞CTree E A i) → CTree E A i

  record ∞CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CTree E A j
```

## Mutual inductive and co-inductive definitions

The semantic functions `eval` and `exec` are well-defined because
recursive calls take smaller arguments (either structurally or
according to some measure), or are guarded by `Later`. For example, in
the case of the lambda calculus, `eval` is applied to the structurally
smaller `x` and `y` in the case of `Add` or is guarded by `Later` in
the case for `App`:

```haskell
eval :: Expr -> Env -> CCTree ChanEff Value
eval (Val n)      e  = return (Num n)
eval (Add x y)    e  = do Num n <- eval x e
                          Num m <- eval y e
                          return (Num (n + m))
eval (Var n)      e  = lookup n e
eval (Abs x)      e  = return (Clo x e)
eval (App x y)    e  = do Clo x' e' <- eval x e
                          v <- eval y e
                          later (eval x' (v : e'))
eval (Send x y)   e  = do Num c <- eval x e
                          Num n <- eval y e
                          send c n
                          return (Num n)
eval (Receive x)  e  = do Num c <- eval x e
                          n <- receive c
                          return (Num n)
eval (Fork x)     e  = do c <- newChan
                          eval x (Num c : e) sp ∥⃗ sp return (Num c)
```

This translates to two mutually recursive functions in Agda, one for
recursive calls (applied to smaller arguments) and one for
co-recursive calls (guarded by `Later`). We use the prefix `∞` to
distinguish the co-recursive function from the recursive function. For
example, for the lambda calculus we write an `eval` and an `∞eval`
function:

```agda
mutual
  eval : ∀ {i} → Expr → Env → CCTree ChanEff Value i
  eval (Val x)     e = return (Num x)
  eval (Add x y)   e = do n ← eval x e >>= getNum
                          m ← eval y e >>= getNum
                          return (Num (n + m))
  eval (Fork x)    e = do ch ← newChan
                          eval x (Num ch ∷ e) ∥⃗ return (Num ch)
  eval (Send x y)  e = do ch ← eval x e >>= getNum
                          n ← eval y e >>= getNum
                          send ch n
                          return (Num n)
  eval (Receive x) e = do ch ← eval x e >>= getNum
                          n ← receive ch
                          return (Num n)
  eval (Abs x)     e = return (Clo x e)
  eval (Var n)     e = lookup n e
  eval (App x y)   e = do x' , e' ← eval x e >>= getClo
                          v ← eval y e
                          later (∞eval x' (v ∷ e'))

  ∞eval : ∀ {i} → Expr → Env → ∞CCTree ChanEff Value i
  force (∞eval x e) = eval x e
```

## Partial pattern matching in do notation

The Haskell syntax in the paper uses partial pattern matching in do
notation, e.g. in the following fragment from section 8.2:

```haskell
eval (Add x y) e = do Num n <- eval x e
                      Num m <- eval y e
                      return (Num (n + m))
```

To represent partial pattern matching in Agda, we use an auxiliary
function (`getNum : ∀ {i} → Value → CCTree e ℕ i` for the code
fragment above) that performs the pattern matching and behaves like
the `fail` method if pattern matches fails:

```agda
eval (Add x y) e = do n ← eval x e >>= getNum
                      m ← eval y e >>= getNum
                      return (Num (n + m))
```

## Codensity choice trees

In the paper, codensity choice trees are defined as elements of type

```haskell
type CCTree e a = forall r . (a -> CTree e r) -> CTree e r
```

subject to two well-formedness properties:

1. if `k x ~ k' x` for all x, then `p k ~ p k'` for all `k, k' :: a ->
  CTree e b`
2. `fmap f (p k) ~ p (\ r -> fmap f (k r))` for all `k:: a -> CTree e
   b f :: b -> c`

In the Agda formalisation, `CCTree` is instead defined syntactically,
i.e.\ as nested inductive coinductive type:

```agda
mutual
  private data CCTree' (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    now'   : (v : A) → CCTree' E A i
    later' : (p : ∞CCTree E A i) → CCTree' E A i
    _⊕'_   : (p q : CCTree' E A i) → CCTree' E A i
    ∅' : CCTree' E A i
    eff'   : ∀ {B} → (e : E B) → (c : B → CCTree' E A i) → CCTree' E A i
    _>>='_ : ∀ {B} → CCTree' E B i → (B → CCTree' E A i) → CCTree' E A i
    _∥⃗'_ : ∀ {B} → CCTree' E B i → CCTree' E A i → CCTree' E A i
    interpSt' : ∀ {F S}  {{_ : Concurrent F}} → S → (∀ {B} → S → F B → CTree E (B × S) ∞) → CCTree' F A i → CCTree' E A i

  record ∞CCTree E (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CCTree' E A j
```

The type `CCTree'` is defined as an abstract type and thus is not
exported. Instead, corresponding synonyms are exported:

```agda
CCTree : (Set → Set) → Set → Size → Set₁
CCTree = CCTree'

now   : ∀ {E A i} (v : A) → CCTree E A i
now = now'

...
```


This syntax for `CCTree` is given a semantics via a semantics function

```agda
⟦_⟧ : ∀ {i A E} {{_ : Concurrent E}} → CCTree E A i → ∀ {R} → (A → CTree E R i) → CTree E R i
```

which defines the semantics of each constructor of `CCTree'` as given
in the paper. For example, the definition of `>>=` in the paper

```haskell
>>= :: CCTree e a -> (a -> CCTree e b) -> CCTree e b
p >>= f = \c -> p (\v -> f v c)
```

translates into the following Agda definition:

```agda
⟦ p >>=' f ⟧ = λ c →  ⟦ p ⟧ (λ v → ⟦ f v ⟧ c)
```

The two well-formedness properties codensity choice trees are then
proved for this syntactically defined notion of codensity choice
trees.

A more straightforward translation of the definition in the paper
would be a sigma type consisting of the semantic notion of codensity
choice trees, i.e. type `∀ {R} → (A → CTree E R i) → CTree E R i`, and
the two well-formedness properties. The above syntactic definition is a
pragmatic alternative formalisation that makes it easier to use
codensity choice trees. For example, this simplifies the definitions
of the above-mentioned functions `eval` and `∞eval`.
