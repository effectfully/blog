-- This blog post is about universe polymorphic programming in Agda.
-- The first part can be found here:
-- [1] http://stackoverflow.com/questions/29179508/arity-generic-programming-in-agda
-- I'll describe how to treat dependent and non-dependent universe polymorphic telescopes
-- more or less uniformly, but to me it looks like a puzzle that is not anyhow important.

open import Level         renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat.Base hiding (_⊔_)
open import Data.Fin      using (Fin; zero; suc)
open import Data.Sum      hiding (map)
open import Data.Product  hiding (map; zip)

record Nil {α} : Set α where
  constructor []

-- We start by defining η-friendly vectors.

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Nil
A ^ suc n = A × A ^ n

-- The difference between `A ^ n` and `Vec A n` is that `A ^ n` can be inferred pointwise.
-- Here is an example.

module Difference where
  open import Data.Unit.Base
  open import Data.Vec

  record Infer {A : Set} (x : A) : Set where

  -- The type signatures of `infer-vec` and `infer-pow` suggest that
  -- if the first and the second elements of a two element vector can be inferred,
  -- then the whole vector can be inferred.

  infer-pow : ∀ {A} {p : A ^ 2} -> Infer (proj₁ p) -> Infer (proj₁ (proj₂ p)) -> ⊤
  infer-pow = _

  infer-vec : ∀ {A} {p : Vec A 2} -> Infer (head p) -> Infer (head (tail p)) -> ⊤
  infer-vec = _

  infer0 : Infer 0
  infer0 = _

  infer1 : Infer 1
  infer1 = _

  -- This is true for our η-friendly vectors:

  ok-infer-pow : ⊤
  ok-infer-pow = infer-pow infer0 infer1

  -- But for usual vectors results in unsolved metas:

  -- fail-infer-vec : ⊤
  -- fail-infer-vec = infer-vec infer0 infer1

  -- _p_72 : Vec ℕ 2
  -- _73 : Infer (head _p_72)
  -- _75 : Infer (head (tail _p_72))

  -- Since we're going to use vectors to store levels which should be inferred,
  -- it's natural to make these vectors η-friendly.
  -- Though, this is not really necessarily in most cases.

-- A universe dependent eliminator for `_^_` (I've never encountered such a thing in nature):

elimPow : ∀ {n α} {A : Set α} {b : ∀ {n} -> A ^ n -> Level}
        -> (B : ∀ {n} -> (xs : A ^ n) -> Set (b xs))
        -> (∀ {n} {xs : A ^ n} x -> B xs -> B (x , xs))
        -> B []
        -> (xs : A ^ n)
        -> B xs
elimPow {0}     B f z  []      = z
elimPow {suc n} B f z (x , xs) = f x (elimPow B f z xs)

-- Some basic functions on `_^_`:

foldr : ∀ {n α β} {A : Set α}
      -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldr B f z xs = elimPow (λ {n} _ -> B n) (λ x y -> f x y) z xs

map : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> A ^ n -> B ^ n
map f = foldr (_ ^_) (_,_ ∘ f) []

foldr₁ : ∀ {n α} {A : Set α} -> (A -> A -> A) -> A ^ suc n -> A
foldr₁ {0}     f (x , []) = x
foldr₁ {suc n} f (x , xs) = f x (foldr₁ f xs)

-- And level-specific ones:

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = flip $ foldr _ _⊔_

max : ∀ {n} -> Level ^ n -> Level
max = _⊔ⁿ lzero

-- `(lsuc lzero , lzero , lift tt) ⊔ⁿ lsuc (lsuc lzero)` reduces to
-- `lsuc lzero ⊔ lzero ⊔ lsuc (lsuc lzero)` (modulo associativity, but Agda has a
-- special treatment of level expression, so associativity doesn't matter).

-- We are now ready to define the type of heterogeneous lists of `Set`s:

Sets′ : ∀ {n} -> (αs : Level ^ n) -> Set (lsuc (max αs))
Sets′ = elimPow (λ αs -> Set (lsuc (max αs))) (λ α R -> Set α × R) Nil

-- I.e. turn each `α` in `αs` into `Set α` and fold the resulting list with `_×_`.

-- An example:

ex-sets : Sets′ (lzero , lsuc lzero , lzero , [])
ex-sets = ℕ , Set , Fin 3 , []

-- The type of telescopes (`Sets` at the link in the first paragraph of this post)
-- can be defined as

Tele′ : ∀ {n} -> (αs : Level ^ n) -> Set (lsuc (max αs))
Tele′ = elimPow (λ αs -> Set (lsuc (max αs))) (λ α R -> Σ (Set α) λ A -> A -> R) Nil

-- It has the same pattern as `Sets′`, but latter elements can depend on former in `Tele′`. E.g.

ex-tele : Tele′ (lzero , lsuc lzero , lzero , [])
ex-tele = ℕ , λ n -> Set , λ _ -> Fin n , λ _ -> []

-- There is a clear pattern: both `Sets′` and `Tele′` are instances of something like

-- `TeleBy′ F = elimPow (Setₘ lsuc) (λ α R -> Σ (Set α) λ A -> F A R) Nil`

-- with

-- `Sets′ = TeleBy′ (λ A R -> R)`
-- `Tele′ = TeleBy′ (λ A R -> A -> R)`

-- But note that universe polymorphic `(λ A R -> R)` and `(λ A R -> A -> R)` have different types:

SetsF : ∀ {α ρ} -> Set α -> Set ρ -> Set ρ
SetsF A R = R

TeleF : ∀ {α ρ} -> Set α -> Set ρ -> Set (α ⊔ ρ)
TeleF A R = A -> R

-- `Set ρ` versus `Set (α ⊔ ρ)`. Hence we need to make `TeleBy′` slightly more generic

TeleBy′ : ∀ {n} {f : Level -> Level -> Level}
        -> (∀ {α ρ} -> Set α -> Set ρ -> Set (f α ρ)) -> (αs : Level ^ n) -> Set _
TeleBy′ {f = f} F = elimPow (λ αs -> Set (foldr _ (λ α ρ -> lsuc α ⊔ f α ρ) lzero αs))
                            (λ α R -> Σ (Set α) λ A -> F A R)
                             Nil

-- Now both `Sets′` and `Tele′` can be defined in terms of `TeleBy′`.
-- But sadly, it's not clear to Agda that `TeleBy′` is constructor-headed,
-- so she can't infer `αs` when a `Tele′ F αs` is provided.
-- This breaks inference and hence we are forced to define `TeleBy` by explicit induction:

TeleBy : ∀ {n} {f : Level -> Level -> Level}
       -> (∀ {α ρ} -> Set α -> Set ρ -> Set (f α ρ))
       -> (αs : Level ^ n)
       -> Set (foldr _ (λ α ρ -> lsuc α ⊔ f α ρ) lzero αs)
TeleBy {0}     F  []      = Nil
TeleBy {suc n} F (α , αs) = Σ (Set α) λ A -> F A (TeleBy F αs)

-- As promised, the definitions of `Sets` and `Tele` are

Sets : ∀ {n} -> (αs : Level ^ n) -> Set (foldr _ (_⊔_ ∘ lsuc) lzero αs)
Sets = TeleBy SetsF

Tele : ∀ {n} -> (αs : Level ^ n) -> Set (foldr _ (_⊔_ ∘ lsuc) lzero αs)
Tele = TeleBy TeleF

-- `Sets` can be mapped over.

mapSets : ∀ {n} {αs : Level ^ n} {f : Level -> Level}
        -> (∀ {α} -> Set α -> Set (f α)) -> Sets αs -> Sets (map f αs)
mapSets {0}     F  []     = []
mapSets {suc n} F (A , R) = F A , mapSets F R

-- Since we have heterogeneous lists of types, we can define heterogeneous lists of values over them.

HList : ∀ {n} {αs : Level ^ n} -> Sets αs -> Set (max αs)
HList {0}      []     = Nil
HList {suc n} (A , R) = A × HList R

-- An example:

ex-hlist : HList (ℕ , Set₁ , Fin 3 , [])
ex-hlist = 0 , Set , suc zero , []

-- As an example of a function defined on heterogeneous lists consider the `lookupʰ` function:

lookup : ∀ {n α} {A : Set α} -> Fin n -> A ^ n -> A
lookup  zero   (x , xs) = x
lookup (suc i) (x , xs) = lookup i xs

lookupˢ : ∀ {n} {αs : Level ^ n} -> (i : Fin n) -> Sets αs -> Set (lookup i αs)
lookupˢ  zero   (A , R) = A
lookupˢ (suc i) (A , R) = lookupˢ i R

lookupʰ : ∀ {n} {αs : Level ^ n} {As : Sets αs} -> (i : Fin n) -> HList As -> lookupˢ i As
lookupʰ  zero   (x , xs) = x
lookupʰ (suc i) (x , xs) = lookupʰ i xs

-- A test:

test-lookupʰ : lookupʰ (suc zero) ex-hlist ≡ Set
test-lookupʰ = refl

-- `Sets` is the type of non-dependent telescopes and `Tele` is the type of dependent telescopes.
-- We can define a function that folds both kinds of telescopes into a functional type:

FoldBy : ∀ {n} {f : Level -> Level -> Level} {αs : Level ^ suc n}
       -> (F : ∀ {α ρ} -> Set α -> Set ρ -> Set (f α ρ))
       -> (∀ {n α} {αs : Level ^ n} {A : Set α} -> F A (TeleBy F αs) -> A -> TeleBy F αs)
       -> TeleBy F αs
       -> Set (foldr₁ _⊔_ αs)
FoldBy {0}     F app (B , _) = B
FoldBy {suc n} F app (A , H) = (x : A) -> FoldBy F app (app H x)

-- Two expected instances are

FoldSets : ∀ {n} {αs : Level ^ suc n} -> Sets αs -> Set (foldr₁ _⊔_ αs)
FoldSets = FoldBy SetsF const

FoldTele : ∀ {n} {αs : Level ^ suc n} -> Tele αs -> Set (foldr₁ _⊔_ αs)
FoldTele = FoldBy TeleF id

-- Examples:

ex-FoldSets : FoldSets (ℕ , Set₁ , Set , []) ≡ (ℕ -> Set₁ -> Set)
ex-FoldSets = refl

ex-FoldTele : FoldTele (ℕ , λ n -> Set₁ , λ _ -> Fin n , λ _ -> []) ≡ (∀ n -> Set₁ -> Fin n)
ex-FoldTele = refl

-- Using `FoldSets` we can define fully universe polymorphic arity-generic `mapⁿ`.

module Mapⁿ where
  open import Data.Vec

  applyⁿ : ∀ {m} n {αs : Level ^ suc n} {As : Sets αs}
         -> Vec (FoldSets As) m -> FoldSets (mapSets (flip Vec m) As)
  applyⁿ  0      xs = xs
  applyⁿ (suc n) fs = λ xs -> applyⁿ n (fs ⊛ xs)

  mapⁿ : ∀ {m} n {αs : Level ^ suc n} {As : Sets αs}
       -> FoldSets As -> FoldSets (mapSets (flip Vec m) As)
  mapⁿ n = applyⁿ n ∘ replicate

  -- `mapⁿ n f xs₁ xs₂ ... xsₙ` evaluates to `replicate f ⊛ xs₁ ⊛ xs₂ ⊛ ... ⊛ xsₙ`.

  -- A test:

  test-mapⁿ : mapⁿ 2 Vec (ℕ ∷ Fin 2 ∷ []) (2 ∷ 1 ∷ []) ≡ Vec ℕ 2 ∷ Vec (Fin 2) 1 ∷ []
  test-mapⁿ = refl

-- In the rest of the post I'll translate the arity-generic machinery described at [1]
-- to this setting. I won't describe it as it's already described there.

module Comp where
  init : ∀ {n α} {A : Set α} -> A ^ suc n -> A ^ n
  init {0}     (x , []) = []
  init {suc n} (x , xs) = x , init xs

  _⋯>ⁿ_ : ∀ {n} {αs : Level ^ suc n} {γ} -> Tele αs -> Set γ -> Set (αs ⊔ⁿ γ)
  _⋯>ⁿ_ {0}     (B , _) C = B -> C
  _⋯>ⁿ_ {suc _} (A , F) C = {x : A} -> F x ⋯>ⁿ C

  Πⁿ : ∀ {n} {αs : Level ^ suc n} {γ} -> (As : Tele αs) -> (As ⋯>ⁿ Set γ) -> Set (αs ⊔ⁿ γ)
  Πⁿ {0}     (B , _) C = (y : B) -> C y
  Πⁿ {suc _} (A , F) C = {x : A} -> Πⁿ (F x) C

  Comp : ∀ n {αs : Level ^ suc n} {γ} {As : Tele αs}
       -> (As ⋯>ⁿ Set γ) -> FoldTele As -> Set (init αs ⊔ⁿ γ)
  Comp  0      C y = C y
  Comp (suc n) C f = ∀ x -> Comp n C (f x)

  comp : ∀ n {αs : Level ^ suc n} {γ} {As : Tele αs} {C : As ⋯>ⁿ Set γ}
       -> Πⁿ As C -> (f : FoldTele As) -> Comp n C f
  comp  0      g y = g y
  comp (suc n) g f = λ x -> comp n g (f x)

  module TestComp where
    open import Data.Bool.Base
    open import Data.Vec

    length : ∀ {α} {A : Set α} {n} -> Vec A n -> ℕ
    length {n = n} _ = n

    explicit-replicate : (A : Set) -> (n : ℕ) -> A -> Vec A n
    explicit-replicate _ _ x = replicate x

    foo : (A : Set) -> ℕ -> A -> ℕ
    foo = comp 3 length explicit-replicate

    test-foo : foo Bool 5 true ≡ 5
    test-foo = refl
