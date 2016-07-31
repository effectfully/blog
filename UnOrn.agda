{-# OPTIONS --type-in-type #-}

-- In this post I'll shortly introduce ornaments and describe an "unbiased" version of them.
-- You might want to read some actual paper first (I recommend [1]).

module UnOrn where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

infixr 0 _∸>_
infixr 6 _⊛_

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set _
A ∸> B = ∀ {i} -> A i -> B i

-- I'll be using the same representation of descriptions as in previous posts.

data Desc (I : Set) : Set where
  var : I -> Desc I
  π   : (A : Set) -> (A -> Desc I) -> Desc I
  _⊛_ : Desc I -> Desc I -> Desc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B i
⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i ≡ j
Extend (π A D) B j = ∃ λ x -> Extend (D x) B j
Extend (D ⊛ E) B j = ⟦ D ⟧ B × Extend E B j

data μ {I} (D : Desc I) j : Set where
  node : Extend D (μ D) j -> μ D j

-- How are a description and its ornamented version related?

-- 1. They both have the same amount of inductive occurrences.
-- Usually this rule sounds like "they both have the same tree structure", but we're going to
-- handle higher-order inductive occurrences which break this pattern.

-- 2. An element of an ornamented data type can always be coerced to the corresponding
-- element of the original data type, i.e. vectors and sorted lists can be coerced to just lists.

-- So when one data type can be coerced to another?

-- 1. If the former simply contains more information that the latter.
-- We throw this information away and get lists from vectors.

-- 2. If the former is an instance of the latter. Here is an example:

module InstExample where
  open import Data.Bool.Base
  open import Data.List.Base

  data D₀ : Set where
    C₀ : ∀ {A} -> List A -> D₀

  data D₁ : Set where
    C₁ : List Bool -> D₁

  D₁→D₀ : D₁ -> D₀
  D₁→D₀ (C₁ xs) = C₀ xs

  -- `D₀` is more general than `D₁` and hence `D₁` can be coerced to `D₀` (condition 2).
  -- Besides, they have the same skeleton (condition 1): both have one non-recursive constructor,
  -- so `D₁` is an ornamented version of `D₀`

-- These are two standard first-order ornaments, but the `Desc` used in this post allows to
-- encode data types with higher-order inductive occurrences, so we have more ornaments as well.

-- 3. If you drop an argument from a higher-inductive occurrence,
-- you'll get an ornamented data type. An example:

module RemoveExample where
  open import Data.Bool.Base
  open import Data.List.Base

  data D₀ : Set where
    C₀ : (Bool -> List Bool -> D₀) -> D₀

  data D₁ : Set where
    C₁ : (Bool -> D₁) -> D₁

  D₁→D₀ : D₁ -> D₀
  D₁→D₀ (C₁ f) = C₀ (λ b _ -> D₁→D₀ (f b))

-- 4. If you add an argument to a higher-order inductive occurrence among with a value
-- from which the argument can be computed, you'll get an ornamented data type as well. An example:

module AddExample where
  open import Data.Bool.Base
  open import Data.Nat.Base
  open import Data.List.Base

  data D₀ : Set where
    C₀ : (Bool -> D₀) -> D₀

  data D₁ : Set where
    C₁ : (Bool -> ℕ × (List Bool -> D₁)) -> D₁

  {-# TERMINATING #-}
  D₁→D₀ : D₁ -> D₀
  D₁→D₀ (C₁ f) = C₀ (λ b -> D₁→D₀ (uncurry (λ n k -> k (replicate n true)) (f b)))

-- This might look silly, but here is how we can combine (2), (3) and (4) in a useful way:

module Example where
  open import Data.Bool.Base
  open import Data.Nat.Base
  open import Data.List.Base

  data D₀ : Set where
    C₀ : (Bool -> D₀) -> D₀

  -- By (4):

  data D₁ : Set where
    C₁ : (Bool -> ℕ × (ℕ -> D₁)) -> D₁

  -- By `(A -> B × C) ≃ (A -> B) × (A -> C)`:

  data D₂ : Set where
    C₂ : ((Bool -> ℕ) × (Bool -> ℕ -> D₂)) -> D₂

  -- By `(A × B -> C) ≃ (A -> B -> C)`:

  data D₃ : Set where
    C₃ : (Bool -> ℕ) -> (Bool -> ℕ -> D₃) -> D₃

  -- By (3):

  data D₄ : Set where
    C₄ : (Bool -> ℕ) -> (ℕ -> D₄) -> D₄

  D₄→D₀ : D₄ -> D₀
  D₄→D₀ (C₄ i f) = C₀ (λ b -> D₄→D₀ (f (i b)))

  -- Note that by (2) we can instantiate `Bool -> ℕ` to, say,
  -- `λ b -> if b then 1 else 0` and thus get

  data D₅ : Set where
    C₅ : (ℕ -> D₅) -> D₅

  -- which is therefore an ornamented version of `D₁`. This inference was a bit long: with
  -- ornaments it's just "remove Bool; add ℕ".

-- So here is how the usual "first-order-biased" ornaments look like

data Con : Set where
  fo ho : Con

module Usual where
  data _⁻¹_ {A B : Set} (f : A -> B) : B -> Set where
    arg : ∀ x -> f ⁻¹ f x

  data Orn {I J : Set} (e : J -> I) : Con -> Desc I -> Set where
    var  : ∀ {i c} -> e ⁻¹ i -> Orn e c (var i)
    keep : ∀ {A D c} -> (∀ x -> Orn e c (D x)) -> Orn e c (π A D)
    _⊛_  : ∀ {D E c} -> Orn e ho D -> Orn e c E -> Orn e c (D ⊛ E)
    abst : ∀ {D} A -> (A -> Orn e fo D) -> Orn e fo D
    inst : ∀ {A D} x -> Orn e fo (D x) -> Orn e fo (π A D)
    drop : ∀ {A D} -> Orn e ho D -> Orn e ho (π A λ _ -> D)
    give : ∀ {A D} -> A -> Orn e ho D -> Orn e ho D

  -- The first three constructors work in any context.
  -- The next two work only in a first-order context.
  -- The last two work only in a higher-order context.

  -- When coercing elements of ornamented data types, we of course need to coerce their indices
  -- as well, so there is a `e : J -> I` that does this.
  
  -- `var` essentially receives a new index `j`, an old index `i` and a proof that `e j ≡ i`.
  -- `keep` simply allows to go under a `π` without touching its content.
  -- Same for `_⊛_`. The first ornament that `_⊛_` receives is always defined in
  -- a higher-order context as it should.

  -- `abst` is for (1): it adds a new argument to a constructor.
  -- `inst` is for (2): it instantiates some argument.
  -- `drop` is for (3): it drops an argument to a higher-order inductive occurrence.
  -- `give` is for (4): it adds a new argument to a higher-order inductive occurrence
  -- and receives a value for it.

  -- Ornaments are interpreted as follows:

  ⟦_⟧ᵒ : ∀ {I J D c} {e : J -> I} -> Orn e c D -> Desc J
  ⟦ var (arg j)  ⟧ᵒ = var j
  ⟦ keep O       ⟧ᵒ = π _ λ x -> ⟦ O x ⟧ᵒ
  ⟦ O ⊛ P        ⟧ᵒ = ⟦ O ⟧ᵒ ⊛ ⟦ P ⟧ᵒ
  ⟦ abst A O     ⟧ᵒ = π A λ x -> ⟦ O x ⟧ᵒ
  ⟦ inst x O     ⟧ᵒ = ⟦ O ⟧ᵒ
  ⟦ drop O       ⟧ᵒ = ⟦ O ⟧ᵒ
  ⟦ give {A} x O ⟧ᵒ = π A λ _ -> ⟦ O ⟧ᵒ

  -- So `abst` and `give` add arguments and `inst` and `drop` remove them as expected.

  -- But look at the type signature of `drop`:

  -- drop : ∀ {A D} -> Orn e ho D -> Orn e ho (π A λ _ -> D)

  -- The second argument of `π` must always ignore its argument. I.e. if we have

  -- data D : Set where
  --   C : (∀ n -> Fin n -> D) -> D

  -- we can't remove `n` even if we remove `Fin n` later too.

  -- `give x` has a similar defect: in a resulting description no type can depend on `x`.

-- Here are unbiased ornaments that don't have these drawbacks:

data Orn {I J : Set} (e : J -> I) : Con -> Desc I -> Desc J -> Set where
  var  : ∀ {j c} -> Orn e c (var (e j)) (var j)
  keep : ∀ {A D E c} -> (∀ x -> Orn e c (D x) (E x)) -> Orn e c (π A D) (π A E)
  _⊛_  : ∀ {D₁ D₂ E₁ E₂ c} -> Orn e ho D₁ E₁ -> Orn e c D₂ E₂ -> Orn e c (D₁ ⊛ D₂) (E₁ ⊛ E₂)
  abst : ∀ {A D E} -> (∀ x -> Orn e fo D (E x)) -> Orn e fo D (π A E)
  inst : ∀ {A D E} x -> Orn e fo (D x) E -> Orn e fo (π A D) E
  drop : ∀ {A D E} -> (∀ x -> Orn e ho (D x) E) -> Orn e ho (π A D) E
  give : ∀ {A D E} x -> Orn e ho D (E x) -> Orn e ho D (π A E)

-- The interpretation of an ornament now is simply the second description that `Orn` receives.

-- Note how the `abst` and `drop` constructors are beautifully symmetric,
-- as well as the `inst` and `give` constructors.

-- `drop` essentially says "you can use the removed "x" as soon as the final result
-- doesn't depend on it". And `give` receives an argument on which other types can depend.

-- Here is a sanity check -- deriving from an ornament its algebra:

Alg : ∀ {I} -> (I -> Set) -> Desc I -> Set
Alg B D = Extend D B ∸> B

forgetHyp : ∀ {I J D E B} {e : J -> I}
          -> (O : Orn e ho D E) -> ⟦ E ⟧ (B ∘ e) -> ⟦ D ⟧ B
forgetHyp  var        y      = y
forgetHyp (keep O)    f      = λ x -> forgetHyp (O x) (f x)
forgetHyp (O ⊛ P)    (x , y) = forgetHyp O x , forgetHyp P y
forgetHyp (drop O)    y      = λ x -> forgetHyp (O x) y
forgetHyp (give x O)  f      = forgetHyp O (f x)

forgetExtend : ∀ {I J D E B} {e : J -> I}
             -> (O : Orn e fo D E) -> Extend E (B ∘ e) ∸> Extend D B ∘ e
forgetExtend  var        refl   = refl
forgetExtend (keep O)   (x , e) = x , forgetExtend (O x) e
forgetExtend (O ⊛ P)    (x , e) = forgetHyp O x , forgetExtend P e
forgetExtend (abst O)   (x , e) = forgetExtend (O x) e
forgetExtend (inst x O)  e      = x , forgetExtend O e

forgetAlg : ∀ {I J D E} {e : J -> I} -> (O : Orn e fo D E) -> Alg (μ D ∘ e) E
forgetAlg O = node ∘ forgetExtend O

-- `drop` removes an argument to a function, so to forget `drop` is to remember that binding.
-- `give` adds an argument and its value, so to forget `give` is to fill the argument with the value.
-- `abst` adds an argument to a constructor, so to forget `abst` is to simply ignore the argument.
-- `inst` specializes an argument to a constructor with some `x`, so to forget `inst` is to
-- apply the original constructor to `x`.

-- Now having the usual catamorphisms stuff

mapHyp : ∀ {I B C} -> (D : Desc I) -> B ∸> C -> ⟦ D ⟧ B -> ⟦ D ⟧ C
mapHyp (var i) g  y      = g y
mapHyp (π A D) g  f      = λ x -> mapHyp (D x) g (f x)
mapHyp (D ⊛ E) g (x , y) = mapHyp D g x , mapHyp E g y

mapExtend : ∀ {I B C} -> (D : Desc I) -> B ∸> C -> Extend D B ∸> Extend D C
mapExtend (var i) g  q      = q
mapExtend (π A D) g (x , e) = x , mapExtend (D x) g e
mapExtend (D ⊛ E) g (x , e) = mapHyp D g x , mapExtend E g e

{-# TERMINATING #-}
gfold : ∀ {I B} {D : Desc I} -> Alg B D -> μ D ∸> B
gfold {D = D} f (node e) = f (mapExtend D (gfold f) e)

-- We can define a generic forgetful map:

forget : ∀ {I J D E} {e : J -> I} -> (O : Orn e fo D E) -> μ E ∸> μ D ∘ e
forget = gfold ∘ forgetAlg

module Tests where
  qvar : ∀ {I J c i j} {e : J -> I} -> e j ≡ i -> Orn e c (var i) (var j)
  qvar refl = var

  -- Ornamenting lists into vectors:

  open import Data.Unit.Base
  open import Data.Bool.Base
  open import Data.Nat.Base

  _<?>_ : ∀ {α} {A : Bool -> Set α} -> A true -> A false -> ∀ b -> A b
  (x <?> y) true  = x
  (x <?> y) false = y

  _⊕_ : ∀ {I} -> Desc I -> Desc I -> Desc I
  D ⊕ E = π Bool (D <?> E)

  infixr 5 _∷_ _∷ᵥ_

  list : Set -> Desc ⊤
  list A = var tt
         ⊕ (π A λ _ -> var tt ⊛ var tt)

  List : Set -> Set
  List A = μ (list A) tt

  vec : Set -> Desc ℕ
  vec A = var 0
        ⊕ π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)

  Vec : Set -> ℕ -> Set
  Vec A = μ (vec A)

  pattern []            = node (true  ,              refl)
  pattern _∷_      x xs = node (false ,     x , xs , refl)
  pattern _∷ᵥ_ {n} x xs = node (false , n , x , xs , refl)

  list→vec : ∀ A -> Orn (λ (_ : ℕ) -> tt) fo (list A) (vec A)
  list→vec A = keep
             $  var
            <?> abst λ n -> keep λ x -> var ⊛ var

  -- A simple test:

  test : forget (list→vec ℕ) (4 ∷ᵥ 9 ∷ᵥ 3 ∷ᵥ 8 ∷ᵥ []) ≡ 4 ∷ 9 ∷ 3 ∷ 8 ∷ []
  test = refl

  -- A more contrived example:

  open import Data.Fin

  data D₀ m : Fin (suc m) -> Set where
    C₀ : (∀ i -> D₀ m (suc i)) -> D₀ m zero

  data D₁ : ℕ -> Set where
    C₁ : (∀ n -> D₁ (suc n)) -> D₁ 0

  coe : ∀ {m} -> ℕ -> Fin (suc m)
  coe {suc m} (suc n) = suc (coe n)
  coe          _      = zero

  coh : ∀ {n} {i : Fin (suc n)} -> coe (toℕ i) ≡ i
  coh {zero } {zero  } = refl
  coh {zero } {suc ()}
  coh {suc n} {zero  } = refl
  coh {suc n} {suc i } = cong suc coh

  D₁→D₀ : ∀ {m n} -> D₁ n -> D₀ m (coe n)
  D₁→D₀ {m} (C₁ f) rewrite coh {m} {zero} = C₀ (λ i -> subst (D₀ _) coh (D₁→D₀ (f (toℕ i))))

  -- We remove `i : Fin m` in `D₀` on which an index depends and replace it with `n` on which
  -- an index depends as well.

  -- And with encoded `D₀` and `D₁`:

  d₀ : ∀ m -> Desc (Fin (suc m))
  d₀ m = (π (Fin m) λ i -> var (suc i)) ⊛ var zero

  d₁ : Desc ℕ
  d₁ = (π ℕ λ n -> var (suc n)) ⊛ var 0

  d₁→d₀ : ∀ m -> Orn coe fo (d₀ m) d₁
  d₁→d₀ m = (drop λ i -> give (toℕ i) (qvar coh)) ⊛ qvar coh

  D₀′ : ∀ m -> Fin (suc m) -> Set
  D₀′ = μ ∘ d₀

  D₁′ : ℕ -> Set
  D₁′ = μ d₁

  D₁′→D₀′ : ∀ {m n} -> D₁′ n -> D₀′ m (coe n)
  D₁′→D₀′ = forget (d₁→d₀ _)

module References where
  -- [1] "Ornamental Algebras, Algebraic Ornaments", Conor McBride
  -- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/LitOrn.pdf
