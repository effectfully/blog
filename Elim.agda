-- This posts describes how to derive eliminators of described data types.

{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

infixr 6 _⊛_

-- I'll be using the form of descriptions introduced in the previous post:
-- http://effectfully.blogspot.com/2016/04/descriptions.html

data Desc I : Set where
  var : I -> Desc I
  π   : ∀ A -> (A -> Desc I) -> Desc I
  _⊛_ : Desc I -> Desc I -> Desc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B i
⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i ≡ j
Extend (π A D) B i = ∃ λ x -> Extend (D x) B i
Extend (D ⊛ E) B i = ⟦ D ⟧ B × Extend E B i

data μ {I} (D : Desc I) j : Set where
  node : Extend D (μ D) j -> μ D j

-- It is crucial to define `μ` as a `data` and not as an inductive `record`,
-- because termination checker works better with `data`s.

-- While defining the generic `elim` function, we'll be keeping in mind some
-- described constructor. Let it be `_∷_` for vectors:

-- `cons-desc = π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)`

module Verbose where
  -- How to get the actual type of the constructor from this description?
  -- Each `π` correspons to some `->` and each `_⊛_` corresponds to it as well.
  -- I.e. the actual type is `(n : ℕ) -> A -> Vec A n -> Vec (suc n)`.
  -- After generalizing `Vec A` to `B`, we get the following definition:

  Cons : ∀ {I} -> (I -> Set) -> Desc I -> Set
  Cons B (var i) = B i
  Cons B (π A D) = ∀ x -> Cons B (D x)
  Cons B (D ⊛ E) = ⟦ D ⟧ B -> Cons B E

  -- `Cons B cons-desc` evaluates to `(n : ℕ) -> A -> B n -> B (suc n)` as required.

  -- Eliminator of `_∷_` (with `Vec A` generalized to `B`) looks like this:

  -- `(n : ℕ) -> (x : A) -> {xs : B n} -> P xs -> P (x ∷ xs)`

  -- so we need to eliminate `cons-desc` again, but now with `_∷_ : Cons B cons-desc` provided
  -- (to form the final `P (x ∷ xs)` part). Note that each inductive occurrence in a description
  -- becomes replaced by the corresponding induction hypothesis, hence the `_⊛_` case
  -- in the function below:

  ElimBy : ∀ {I B} -> ((D : Desc I) -> ⟦ D ⟧ B -> Set) -> (D : Desc I) -> Cons B D -> Set
  ElimBy P (var i) x = P (var i) x
  ElimBy P (π A D) f = ∀ x -> ElimBy P (D x) (f x)
  ElimBy P (D ⊛ E) f = ∀ {x} -> P D x -> ElimBy P E (f x)

  -- The type of `P` is `(D : Desc I) -> ⟦ D ⟧ B -> Set` instead of `∀ {i} -> B i -> Set`,
  -- because there can be a higher-order inductive occurrence (like in `W`) and
  -- the induction hypothesis have to be computed by induction on a `Desc`.
  -- We'll do this in a moment.

  -- The next step is to compute the constructor.
  -- As described in the previous post the actual `_∷_` can be recovered as
  
  -- `_∷_ {n} x xs = node (n , x , xs , refl)`

  -- (it's `node (false, n , x , xs , refl)` for the actual `Vec`,
  -- because the first element in a tuple allows to distinguish `[]` and `_∷_`)

  -- So all we need is to define a function that receives `n` arguments,
  -- puts them in a tuple and applies `node` to it. That's the usual CPS stuff:

  cons : ∀ {I B} -> (D : Desc I) -> (∀ {j} -> Extend D B j -> B j) -> Cons B D
  cons (var i) k = k refl
  cons (π A D) k = λ x -> cons (D x) (k ∘ _,_ x)
  cons (D ⊛ E) k = λ x -> cons  E    (k ∘ _,_ x)

  -- However note that `ElimBy` and `cons` are defined by the same induction on `D`.
  -- Hence we can drop `Cons` and `cons` stuff and compute `ElimBy` directly.

-- Here is the final definition of `ElimBy`:

ElimBy : ∀ {I B}
       -> ((D : Desc I) -> ⟦ D ⟧ B -> Set)
       -> (D : Desc I)
       -> (∀ {j} -> Extend D B j -> B j)
       -> Set
ElimBy C (var i) k = C (var i) (k refl)
ElimBy C (π A D) k = ∀ x -> ElimBy C (D x) (k ∘ _,_ x)
ElimBy C (D ⊛ E) k = ∀ {x} -> C D x -> ElimBy C E (k ∘ _,_ x)

-- Now we need to compute induction hypotheses. Recall how `W` looks like:

data W (A : Set) (B : A -> Set) : Set where
  sup : ∀ x -> (B x -> W A B) -> W A B

-- Its eliminator is

elimW : ∀ {α β π} {A : Set α} {B : A -> Set β}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : B x -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW P h (sup x g) = h (λ y -> elimW P h (g y))

-- I.e. the induction hypothesis for higher-order `g : B x -> W A B` is
-- `(y : B x) -> P (g y)` (higher-order as well).

Hyp : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> ⟦ D ⟧ B -> Set
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x) 
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

-- When an inductive occurrence is a tuple, the induction hypothesis is a tuple too,
-- hence the `_⊛_` case above.

-- Finally, the type of a function that eliminator receives
-- (I'll call it "an eliminating function") is

Elim : ∀ {I B}
     -> (∀ {i} -> B i -> Set)
     -> (D : Desc I)
     -> (∀ {j} -> Extend D B j -> B j)
     -> Set
Elim = ElimBy ∘ Hyp

-- It only remains to construct the actual generic eliminator.

module _ {I} {D₀ : Desc I} (P : ∀ {j} -> μ D₀ j -> Set) (h : Elim P D₀ node) where
  mutual
    elimExtend : ∀ {j}
               -> (D : Desc I) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
               -> Elim P D k
               -> (e : Extend D (μ D₀) j)
               -> P (k e)
    elimExtend (var i) z  refl   = z
    elimExtend (π A D) h (x , e) = elimExtend (D x) (h  x)        e
    elimExtend (D ⊛ E) h (d , e) = elimExtend  E    (h (hyp D d)) e

    hyp : ∀ D -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp P D d
    hyp (var i)  d      = elim d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (x , y) = hyp D x , hyp E y

    elim : ∀ {j} -> (d : μ D₀ j) -> P d
    elim (node e) = elimExtend D₀ h e

-- No surpise we need a family of mutually defined functions.
-- `D₀` is the description of a data being eliminated. It's in the module parameter
-- among with `P` and an eliminating function `h`, because otherwise it would be required
-- to trace them explicitly through all three functions and these parameters never change.

-- `elim` unfolds a `μ` and delegates the work to `elimExtend`.

-- `elimExtend` is defined by induction on `D`:
-- - At the end of a description we simply return what has been computed so far.
-- - On encountering a non-inductive argument to a constructor we
--     apply the eliminating function to it.
-- - On encountering an inductive argument to a constructor we
--     compute recursively (`hyp` calls `elim` in the `var` case) and
--     apply the elimination function to the result of the computation.

-- That's basically it. An example:

open import Data.Bool.Base
open import Data.Nat.Base

_<?>_ : ∀ {α} {A : Bool -> Set α} -> A true -> A false -> ∀ b -> A b
(x <?> y) true  = x
(x <?> y) false = y

_⊕_ : ∀ {I} -> Desc I -> Desc I -> Desc I
D ⊕ E = π Bool (D <?> E)

vec : Set -> Desc ℕ
vec A = var 0
      ⊕ π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)

Vec : Set -> ℕ -> Set
Vec A = μ (vec A)

pattern []           = node (true  , refl)
pattern _∷_ {n} x xs = node (false , n , x , xs , refl)

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z = elim P (z <?> λ _ -> f)

-- Since vectors have two constructors, `vec` starts with `π Bool` which allows to split
-- the description into two parts: the one that describes `[]` and the other that describes `_∷_`.
-- That's why an eliminating function for vectors is of the form `(b : Bool) -> ...` and
-- we use `_<?>_` to choose between an eliminating function for `[]` (just a value `z`) and
-- an eliminating function for `_∷_` (which ignores `n : ℕ`).
