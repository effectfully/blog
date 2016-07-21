-- In this post I'll show how to emulate cumulativity in Agda.

module Cumu where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

-- As an example let's take telescopes.
-- Recall how they can be defined without universe polymophism:

module Mono where
  open import Data.Unit.Base
  open import Data.Nat.Base
  open import Data.Vec

  infix 3 _▷_

  data Tele : Set₁ where
    ε   : Tele
    _▷_ : (A : Set) -> (A -> Tele) -> Tele

  -- `_▷_` receives a type `A` and the rest of a telescope,
  -- where each type can depend on an element of type `A`.

  -- Here is an example:

  example : Tele
  example = ℕ ▷ λ n -> Vec ℕ n ▷ λ _ -> ε

  -- Each telescope represents the type of an n-ary tuples:

  ⟦_⟧ : Tele -> Set
  ⟦ ε     ⟧ = ⊤
  ⟦ A ▷ R ⟧ = Σ A λ x -> ⟦ R x ⟧

  test : ⟦ example ⟧ ≡ ∃ λ n -> Vec ℕ n × ⊤
  test = refl

  -- The problem with this encoding however is that `_▷_` always receives a `Set`,
  -- while we want it to receive types from different universes. How can we achieve that?

-- We could define `Tele` by recursion on a list of levels like this:

module Rec where
  open import Data.Unit.Base
  open import Data.List.Base

  Tele : ∀ αs -> Set (foldr (_⊔_ ∘ lsuc) lzero αs)
  Tele  []      = ⊤
  Tele (α ∷ αs) = Σ (Set α) λ A -> A -> Tele αs

  -- This is the same `Tele` as above, but now universe polymorphic:

  example : Tele (lsuc lzero ∷ lzero ∷ lsuc (lsuc lzero) ∷ [])
  example = Set , λ A -> A , λ _ -> Set₁ , λ _ -> tt

  -- The problem with this encoding however is that all levels are explictly reflected
  -- at the type level (in this case they can be inferred, since `Tele` is constructor-headed).
  -- It means that there can't exist telescopes with statically unknown length:

  -- fail : ∃ Tele
  -- fail = ?

  -- ((αs : List Level) → Set (foldr ((λ {.x} → _⊔_) ∘ lsuc) lzero αs))
  -- !=< (_A_38 → Set _b_37)
  -- because this would result in an invalid use of Setω
  -- when checking that the expression Tele has type _A_38 → Set _b_37

  -- What we really want is to write `Tele (lsuc (lsuc lzero))`,
  -- i.e. just one level -- the biggest -- and make Agda check that all other levels
  -- are less or equal than it. And doesn't reflect the length of a telescope at the type level.
  -- I.e. just what we normally do:

  example₂ : Set₂
  example₂ = Σ Set λ A -> A × Set₁ × ⊤

record ⊤ {α} : Set α where
  constructor tt

-- We can state that one level is less or equal than another as follows:

_≤ℓ_ : Level -> Level -> Set
α ≤ℓ β = α ⊔ β ≡ β

-- I.e. if the maximum of `α` and `β` is `β`, then `α` is obviously less or equal than `β`.

-- We need a way to coerce a `Set α` to `Set β`, provided there is a proof of `α ≡ β`.
-- It can be done either by a function:

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

-- or using a data type:

data Coerce {β} : ∀ {α} -> α ≡ β -> Set α -> Set β where
  coerce : ∀ {A} -> A -> Coerce refl A

-- We'll need both of them.

-- Here is the encoding finally:

{-# NO_POSITIVITY_CHECK #-}
data Tele β : Set (lsuc β) where
  ε    : Tele β
  cons : ∀ {α} -> (q : α ≤ℓ β) -> Coerce (cong lsuc q) (∃ λ (A : Set α) -> A -> Tele β) -> Tele β

-- Operationally it's the same as before: `cons` receives a type `A` and the rest of a telescope,
-- but now `A` lies in `Set α` and we have an explicit proof that `α` is less or equal than `β`.

-- The type of `∃ λ (A : Set α) -> A -> Tele β` is `Set (lsuc α ⊔ lsuc β)` which is the same as
-- `Set (lsuc (α ⊔ β))`, but it must lie in `Set (lsuc β)`, because the whole `Tele` lies there,
-- so we coerce by `cong lsuc q : lsuc (α ⊔ β) ≡ lsuc β` and get the required type.

-- The constructor is recovered as

pattern _▷_ A R = cons _ (coerce (A , R))

-- Though, it's not possible to use it in pattern matching,
-- because that would force unification of `lsuc (α ⊔ β) =?= lsuc β`,
-- which is an infinite equation that can't be solved.

-- An example:

example : Tele (lsuc (lsuc lzero))
example = Set ▷ λ A -> A ▷ λ _ -> Set₁ ▷ λ _ -> ε

-- All types lie in different universes and `Tele` receives only the level of the biggest universe.

-- It only remains to interpret telescopes:

mutual
  ⟦_⟧ᵀ : ∀ {β} -> Tele β -> Set β
  ⟦ ε ⟧ᵀ        = ⊤
  ⟦ cons q B ⟧ᵀ = ⟦ B ⟧ᵀᵇ q

  ⟦_⟧ᵀᵇ : ∀ {α β γ q} -> Coerce {β = γ} q (∃ λ (A : Set α) -> A -> Tele β) -> α ≤ℓ β -> Set β
  ⟦ coerce (A , R) ⟧ᵀᵇ q = Coerce′ q (∃ λ x -> ⟦ R x ⟧ᵀ)

-- It's the same as before, but we need two functions and one additional `Coerce′`.
-- Two functions are needed, because, as was mentioned above, it's not possible to use `_▷_`
-- in pattern matching, so the levels equation is generalized to `lsuc (α ⊔ β) =?= γ`,
-- which can be solved. `Coerce′` is needed, because `∃ λ x -> ⟦ R x ⟧ᵀ` lies in `Set (α ⊔ β)`,
-- while we want it to be in `Set β`. Note that `Coerce′` is just a function and
-- doesn't introduce mess in the interpretation of a telescope.

-- A simple test:

test : ⟦ example ⟧ᵀ ≡ ∃ λ A -> A × Set₁ × ⊤
test = refl

-- We have considered how to emulate cumulativity for telescopes,
-- but there are other applications: convenient universe polymorphic descriptions
-- (I'm working on a generic programming library that uses ideas described in this post),
-- universe polymorphic Freer monads (as described by Kiselyov et al) for dealing with effects,
-- perhaps something else.
