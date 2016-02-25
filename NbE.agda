-- Stealing an intro from sigfpe ([1]),
-- I've decided that Normalization by Evaluation is the hardest trivial thing in type theory.
-- Let's go down the rabbit hole.

module NbE where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat.Base
open import Data.Sum
open import Data.List.Base

module Readback where
  infixr 3 ƛ_
  infixl 6 _·_ _∙_

  -- NbE is usually explained like this:
  -- 1. first-order lambda terms representation
  -- 2. higher-order lambda terms representation
  -- 3. `readback'
  -- 4. `eval`
  -- 5. `norm = readback ∘ eval`

  -- Our plan is as follows:
  -- 1. higher-order lambda terms representation
  -- 2. normalization for higher-order lambda terms
  -- 3. first-order lambda terms representation
  -- 4. `toValue`, `fromValue`
  -- 5. `norm = fromValue ∘ normValue ∘ toValue`
  -- 6. `eval`
  -- 7. `norm = readback ∘ eval`

  -- The higher-order lambda terms representation is
  
  {-# NO_POSITIVITY_CHECK #-}
  data Value (A : Set) : Set where
    pure : A -> Value A
    lam  : (Value A -> Value A) -> Value A
    _·_  : Value A -> Value A -> Value A

  VTerm : Set₁
  VTerm = ∀ {A} -> Value A

  -- A few examples:

  Iᵥ : VTerm
  Iᵥ = lam λ x -> x

  Kᵥ : VTerm
  Kᵥ = lam λ x -> lam λ y -> x

  Sᵥ : VTerm
  Sᵥ = lam λ f -> lam λ g -> lam λ x -> f · x · (g · x)

  -- It might be instructive to add some parentheses:

  S⁽⁾ : VTerm
  S⁽⁾ = lam (λ f -> lam (λ g -> lam (λ x -> f · x · (g · x))))

  -- `lam` receives a continuation that returns a `Value`.
  -- "Continuations are programs with holes in them" (quoted from [2]),
  -- so `S` says "give me some `f`, `g` and `x`" and I'll produce `f · x · (g · x)` to you".
  -- But these `f`, `g` and `x` are themselves `VTerm`s,
  -- hence we can define function application that β-reduces:

  _∙_ : ∀ {A} -> Value A -> Value A -> Value A
  lam k ∙ x = k x
  f     ∙ x = f · x

  -- If the head constructor is `lam`, then there is a hole that we can fill.
  -- Otherwise we simply use the `_·_` constructor.

  -- A simple test:

  SI : ∀ {A} -> Sᵥ {A} ∙ Iᵥ ≡ lam λ g -> lam λ x -> Iᵥ · x · (g · x)
  SI = refl

  -- `f` was substituted by `Iᵥ`.

  -- Normalization of a `Value` is similar:

  {-# TERMINATING #-}
  normValue : ∀ {A} -> Value A -> Value A
  normValue (pure x) = pure x
  normValue (lam k ) = lam λ x -> normValue (k x)
  normValue (f · x ) = case normValue f of λ
    { (lam k) -> normValue (k x)
    ;  nf     -> nf · normValue x
    }

  -- In the `f · x` case we first normalize `f`, if the head constructor is `lam`,
  -- then there is a hole, we fill it and proceed further. Otherwise
  -- `normValue (f · x)` is the same as `normValue f · normValue x`.

  -- An example:

  SKK : normValue (Sᵥ · Kᵥ · Kᵥ · pure 0) ≡ normValue (Iᵥ · pure 0)
  SKK = refl

  -- The first-order representation of lambda terms will contain de Bruijn indices

  data Term : Set where
    var : ℕ -> Term
    ƛ_  : Term -> Term
    _·_ : Term -> Term -> Term

  -- A few examples:

  I : Term
  I = ƛ var 0

  K : Term
  K = ƛ ƛ var 1

  S : Term
  S = ƛ ƛ ƛ var 2 · var 0 · (var 1 · var 0)

  -- Here is a function that converts higher-order lambda terms to theiry first-order counterparts:

  var⁺ : ℕ -> ℕ -> Term
  var⁺ m n = var (n ∸ m ∸ 1)

  fromValue : VTerm -> Term
  fromValue x = go 0 x where
    go : ℕ -> Value ℕ -> Term
    go n (pure m) = var⁺ m n
    go n (lam k ) = ƛ (go (suc n) (k (pure n)))
    go n (f · x ) = go n f · go n x

  -- In `go` `n` represents the number of already encountered lambda abstractions.
  -- On encountering a `lam`, we prepend a lambda to the resulting term and
  -- apply the continuation to a fresh variable represented as a number of encountered
  -- lambdas wrapped in `pure`. We also increase the lambdas counter.
  -- In the `go n (pure m)` case we know that some variable was substituted by `pure m`,
  -- where `m` was a number of encountered so far lambdas.
  -- And now the number of encountered lambdas is `n`.
  -- Thus, the resulting de Bruijn index is `n ∸ m ∸ 1`. 

  -- Here are some reductions:

  -- `fromValue Iᵥ`
  -- `go 0 (lam λ x -> x)`
  -- `ƛ (go 1 (pure 0))`
  -- `ƛ var vz`

  -- `fromValue Kᵥ`
  -- `go 0 (lam λ x -> lam λ y -> x)`
  -- `ƛ (go 1 (lam λ y -> pure 0))`
  -- `ƛ ƛ (go 2 (pure 0))`
  -- `ƛ ƛ var 1`

  Sᵥ≈S : fromValue Sᵥ ≡ S
  Sᵥ≈S = refl

  -- We'll need some unsafe silliness in order to define the `toValue` function.
  
  module _ where
    postulate undefined : ∀ {α} {A : Set α} -> A

    unsafeLookup : ∀ {α} {A : Set α} -> ℕ -> List A -> A
    unsafeLookup  _       []      = undefined
    unsafeLookup  0      (x ∷ xs) = x
    unsafeLookup (suc n) (x ∷ xs) = unsafeLookup n xs

  toValue : Term -> VTerm
  toValue t = go [] t where
    go : ∀ {A} -> List (Value A) -> Term -> Value A
    go ρ (var n) = unsafeLookup n ρ
    go ρ (ƛ b  ) = lam (λ x -> go (x ∷ ρ) b)
    go ρ (f · x) = go ρ f · go ρ x

  -- In `go` `ρ` is an environment -- a list of already introduced bindings.
  -- When encounter a `ƛ`, we prepend `lam` to the result, bind a variable
  -- and add this binding to the environment. Later, in the `var n` case we take the nth binding.

  -- Here are some reductions:

  -- `toValue I`
  -- `go [] (ƛ var 0)`
  -- `lam λ x -> go (x ∷ []) (var 0)`
  -- `lam λ x -> x`

  -- `toValue K`
  -- `go [] (ƛ ƛ var 1)`
  -- `lam λ x -> go (x ∷ []) (ƛ var 1)`
  -- `lam λ x -> lam λ y -> go (y ∷ x ∷ []) (var 1)`
  -- `lam λ x -> lam λ y -> x`

  S≈Sᵥ : ∀ {A} -> toValue S {A} ≡ Sᵥ
  S≈Sᵥ = refl

  -- Finally, the normalization function:

  norm′ : Term -> Term
  norm′ t = fromValue (normValue (toValue t))

  SKK≈I′ : norm′ (S · K · K) ≡ I
  SKK≈I′ = refl

  -- `norm` is usually defined in terms of `readback` (or `quote`) and `eval`.
  -- `readback` is the same thing as `fromValue`

  readback : VTerm -> Term
  readback = fromValue

  -- and `eval` is like `normValue ∘ toValue`, but in one phase:

  eval : Term -> VTerm
  eval t = go [] t where
    go : ∀ {A} -> List (Value A) -> Term -> Value A
    go ρ (var n) = unsafeLookup n ρ
    go ρ (ƛ b  ) = lam (λ x -> go (x ∷ ρ) b)
    go ρ (f · x) = go ρ f ∙ go ρ x

  -- The only difference between toValue` and `eval` is that function application
  -- β-reduces in the latter case, i.e. it's `go ρ f ∙ go ρ x` instead of `go ρ f · go ρ x`.

  norm : Term -> Term
  norm = readback ∘ eval

  SKK≈I : norm (S · K · K) ≡ I
  SKK≈I = refl

  S≈S : norm S ≡ S
  S≈S = refl

module NewValues where
  open Readback using (Term; var; ƛ_; _·_; var⁺; unsafeLookup; I; K; S) public

  infixl 6 _·⁺_ _∙_

  -- Our next step is to remove `_·_` from `Value`s and define normalization within this setting.

  {-# NO_POSITIVITY_CHECK #-}
  data Value (A : Set) : Set where
    pure : A -> Value A
    lam  : (Value A -> Value A) -> Value A

  -- With the de Bruijn indices approach a variable can be denoted by different indices in a term,
  -- depending on how many variables were introduced after it.
  -- E.g. consider the `ω` combinator: `ƛ var 0 · var 0`. We can η-expand the last `var 0` and get
  -- `ƛ var 0 · (ƛ var 1 · var 0)`. The variable introduced by the first lambda is denoted
  -- first as `var 0` and then as `var 1`.

  -- It's a problem, because we want to fill a hole in a term `lam λ x -> ...`
  -- by passing something to the continuation, so `x` will everywhere be replaced by
  -- some expression. But de Bruijn indices are context dependent, so it's not possible to
  -- do that with them.

  -- There is no such problem with de Bruijn levels (e.g. the `S` combinator with
  -- de Bruijn levels is represented as `ƛ ƛ ƛ var 0 · var 2 · (var 1 · var 2)`).
  -- The `ω` combinator with de Bruijn levels is the same `ƛ var 0 · var 0`,
  -- but if we now η-expand the last `var 0`, we'll get `ƛ var 0 · (ƛ var 0 · var 1)`.
  -- The variable introduced by the first lambda is `var 0` everywhere.

  -- The solution is to emulate de Bruijn levels using the liftable terms approach
  -- (the terminology is due to [3]). Instead of instantiating `x` in `lam λ x -> ...` with
  -- a term, we'll instantiate it with a function that returns a term. Lately, the function
  -- will be applied to the number of encountered lambdas and will compute the term
  -- accordingly to this context.

  -- Liftable terms are

  Term⁺ : Set
  Term⁺ = ℕ -> Term

  -- We have already seen liftable variables:

  -- var⁺ : ℕ -> ℕ -> Term
  -- var⁺ m n = var (n ∸ m ∸ 1)

  -- Function application for liftable terms is straightforward:

  _·⁺_ : Term⁺ -> Term⁺ -> Term⁺
  (f ·⁺ x) n = f n · x n

  -- As promised terms in the model are

  VTerm : Set
  VTerm = Value Term⁺

  -- `readback` receives a `VTerm` and a number of already encountered lambdas.

  readback : VTerm -> Term⁺
  readback (pure t) n = t n
  readback (lam k)  n = ƛ (readback (k (pure (var⁺ n))) (suc n))

  -- On encountering `lam λ x -> ...` `x` gets instantiated to `pure (var⁺ n)` --
  -- recall that `var⁺ n m` returns the de Bruijn index of a variable introduced by `n`th lambda
  -- in a context with `m` lambdas. We also increase the lambdas counter by `suc n`.

  -- Function application for values is

  _∙_ : VTerm -> VTerm -> VTerm
  pure f ∙ x = pure (f ·⁺ readback x)
  lam k  ∙ x = k x

  -- The `lam` case is the same. `_∙_` is used such that in the `pure` case
  -- `f` is always a neutral term and hence `x` can safely be readback -- it won't participate
  -- in β-reductions. So this is how we construct terms: we collect function applications
  -- under the `pure` wrapper.

  -- `eval` is the same as before.

  eval : Term -> VTerm
  eval = go [] where
    go : List VTerm -> Term -> VTerm
    go ρ (var n) = unsafeLookup n ρ
    go ρ (ƛ b  ) = lam (λ x -> go (x ∷ ρ) b)
    go ρ (f · x) = go ρ f ∙ go ρ x

  norm : Term -> Term
  norm t = readback (eval t) 0

  -- Let's now look at an example.

  ηω : Term
  ηω = ƛ var 0 · (ƛ var 1 · var 0)

  -- `norm ηω` reduces like this:
  
  -- expand all definitions:
  -- `norm ηω`
  -- `readback (eval ηω) 0`
  -- `readback (lam λ x -> x ∙ (lam λ y -> x ∙ y)) 0`

  -- `readback` consumes `lam`:
  -- `ƛ readback (pure (var⁺ 0) ∙ (lam λ y -> pure (var⁺ 0) ∙ y)) 1`

  -- `_∙_` fires:
  -- `ƛ readback (pure (var⁺ 0 ·⁺ readback (lam λ y -> pure (var⁺ 0) ∙ y))) 1`

  -- `readback` consumes `pure`:
  -- `ƛ (var⁺ 0 ·⁺ readback (lam λ y -> pure (var⁺ 0) ∙ y)) 1`

  -- `_·⁺_` fires:
  -- `ƛ var⁺ 0 1 · readback (lam λ y -> pure (var⁺ 0) ∙ y)) 1`

  -- `var⁺ 0 1` reduces:
  -- `ƛ var 0 · readback (lam λ y -> pure (var⁺ 0) ∙ y)) 1`

  -- `readback` consumes `lam`:
  -- `ƛ var 0 · (ƛ readback (pure (var⁺ 0) ∙ pure (var⁺ 1)) 2)`

  -- `_∙_` fires:
  -- `ƛ var 0 · (ƛ readback (pure (var⁺ 0 ·⁺ readback (pure (var⁺ 1)))) 2)`

  -- `readback`s consume `pure`s:
  -- `ƛ var 0 · (ƛ (var⁺ 0 ·⁺ var⁺ 1) 2)`

  -- `_·⁺_` fires
  -- `ƛ var 0 · (ƛ var⁺ 0 2 · var⁺ 1 2)`

  -- `var⁺` reduce:
  -- `ƛ var 0 · (ƛ var 1 · var 0)`

  -- and we're done.

  -- The key point is that the number of encountered lambdas is traced over the whole computation.
  -- `_·⁺_` "distributes" it, `var⁺` and `readback` consume it. `_∙_` "resumes" `readback`:

  -- `pure f ∙ x = pure (f ·⁺ readback x)`

  -- and it always starts at the point where the previous `readback` stopped
  -- (i.e. with the same amount of encountered lambdas), where "stopping" is

  -- `readback (pure t) n = t n`

  -- This also explains why we can't simply use de Bruijn levels -- it's anyway necessarily to
  -- trace a number of encountered lambdas to be able to resume `readback`.

module Reify&Reflect where
  open NewValues hiding (readback; _∙_; eval; norm)

  infixr 6 _⇒_

  -- There is another standard variant of Normalization by Evaluation:
  -- in terms of `reify` and `reflect`. It's type-directed, so we'll need some types for it:

  data Type : Set where
    ⋆   : Type
    _⇒_ : Type -> Type -> Type

  postulate undefined : ∀ {α} {A : Set α} -> A

  -- Function application that β-reduces remains the same for the `lam` case
  -- and becomes undefined otherwise.

  _∙_ : ∀ {A} -> Value A -> Value A -> Value A
  pure _ ∙ x = undefined
  lam k  ∙ x = k x

  -- `eval` is the same.

  eval : ∀ {A} -> Term -> Value A
  eval t = go [] t where
    go : ∀ {A} -> List (Value A) -> Term -> Value A
    go ρ (var n) = unsafeLookup n ρ
    go ρ (ƛ b  ) = lam (λ x -> go (x ∷ ρ) b)
    go ρ (f · x) = go ρ f ∙ go ρ x

  -- The core of the approach:

  mutual
    reify : Type -> VTerm -> Term⁺
    reify  ⋆      (pure t) n = t n
    reify (σ ⇒ τ) (lam k)  n = ƛ (reify τ (k (rvar⁺ σ n)) (suc n))
    reify  _       _       n = undefined

    reflect : Type -> Term⁺ -> VTerm
    reflect  ⋆      t = pure t
    reflect (σ ⇒ τ) f = lam λ x -> reflect τ (f ·⁺ reify σ x)

    rvar⁺ : Type -> ℕ -> VTerm
    rvar⁺ σ n = reflect σ (var⁺ n)

  norm : Type -> Term -> Term
  norm σ t = reify σ (eval t) 0

  -- Compare `reify` to `readback`:

  -- readback : VTerm -> Term⁺
  -- readback (pure t) n = t n
  -- readback (lam k)  n = ƛ (readback (k (pure (var⁺ n))) (suc n))

  -- They are very similar except that in `readback` `k` receives `pure (var⁺ n)`
  -- and in `reify` `k` receives `reflect σ (var⁺ n)` (after unfolding `rvar⁺ σ n`).
  -- `reify` is also type-directed, hence it performs full η-expansion.

  -- So what's the difference between `pure (var⁺ n)` and `reflect σ (var⁺ n)`?
  -- `reflect` performs η-expansion of values.

  -- Recall how `_∙_` was defined in the previous section:

  -- _∙_ : VTerm -> VTerm -> VTerm
  -- pure f ∙ x = pure (f ·⁺ readback x)
  -- lam k  ∙ x = k x

  -- With this definition `pure (var⁺ n) ∙ x` reduces to `pure (var⁺ n ·⁺ readback x)`.
  -- `reflect` allows to reduce the expression in the same way while leaving `_∙_` undefined
  -- in the `pure` case. Instead, both the tasks of performing β-reductions and collecting
  -- function applications under the `pure` wrapper we solve using just `lam`.

  -- Consider `rvar⁺ (⋆ ⇒ ⋆) n ∙ x`. It reduces to `(lam λ y -> pure (var⁺ n ·⁺ reify σ y)) ∙ x`
  -- and further to `pure (var⁺ n ·⁺ reify σ x)`. Just the same expression as before
  -- (keep in mind that `reify` is a new version of `readback`).

  -- That's basically it. The `reify&reflect` approach is just the `readback` approach
  -- after some reshuffling.

module Typed where
  -- The next step is to define normalization for Church-like typed terms.
  -- It's straightforward to adapt the liftable terms approach to typed setting
  -- (though, it still costs a `postulate`). An implementation can be found here:

  -- https://github.com/effectfully/random-stuff/blob/master/Normalization/Liftable.agda

  -- Note that this approach allows to get a first-order representation
  -- of a pure Agda lambda term, see the examples at the end of the file.
  
  -- The implementation is in terms of `reify` and `reflect`. It's adapted from [4].

  -- But the actual magic happens when you interpret function space of the target language
  -- in a Kripke-like fashion and thus incorporate weakening into semantics.
  -- I'm not very comfortable with this approach, so I won't describe it either, but
  -- a minimal implementation (in terms of `readback`) can be found here:

  -- https://github.com/effectfully/random-stuff/blob/master/Normalization/Readback.agda

module References where
  -- [1] "Reverse Engineering Machines with the Yoneda Lemma"
  -- Dan Piponi
  -- http://blog.sigfpe.com/2006/11/yoneda-lemma.html

  -- [2] http://stackoverflow.com/a/32146054/3237465

  -- [3] "Normalization by Evaluation for Martin-Löf Type Theory with One Universe"
  -- Andreas Abel, Klaus Aehlig, Peter Dybjer
  -- http://www.cse.chalmers.se/~peterd/papers/NbeMLTT.pdf

  -- [4] "Normalization by Evaluation, Dependent Types and Impredicativity"
  -- Andreas Abel
  -- http://www.cse.chalmers.se/~abela/habil.pdf
