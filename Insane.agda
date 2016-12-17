{-# OPTIONS --type-in-type #-} -- This is needed only for the `InductiveInductive` module.

-- In this post I'll show a technique that allows to describe nearly all Agda data types,
-- including non-strictly positive and inductive-inductive ones.
-- You'll also see how insanely dependent types can be emulated in Agda.
-- The reader is assumed to be familiar with descriptions.

module Insane where

-- Preliminaries:

open import Level using (_⊔_)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat.Base hiding (_⊔_)
open import Data.Fin
open import Data.Sum     hiding (map)
open import Data.Product hiding (map)

infixr 0 _∸>_ _⇒_

record ⊤ {α} : Set α where
  constructor tt

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set (ι ⊔ α ⊔ β)
A ∸> B = ∀ {i} -> A i -> B i

unsubst : ∀ {α β γ} {A : Set α} {B : A -> Set β} {x y}
        -> (C : ∀ x -> B x -> Set γ) {z : B x}
        -> (q : x ≡ y)
        -> C y (subst B q z)
        -> C x  z
unsubst C refl = id

-- Here is how we describe a constructor of a data type:

data Cons (I : Set) : Set₁ where
  ret : I -> Cons I
  π   : (A : Set) -> (A -> Cons I) -> Cons I

-- You're perhaps wondering where I hide inductive occurrences. They are handled by `π`
-- just like non-inductive arguments to constructors. It means that we can't distinguish
-- between inductive and non-inductive arguments by means of pattern matching and hence
-- can't e.g. define a generic `depth` function. So the encoding is far from being perfect,
-- but it does allow to define generic `_≟_`, `show` and similar functions
-- (using instance arguments). An example in a similar system can be found in [4].

-- Here is how we can describe the type of Vec's `_∷_`:

-- `VCons = π ℕ λ n -> π A λ _ -> π (Vec A n) λ _ -> ret (suc n)`

-- Interpretation of described constructors goes as follows:

⟦_⟧ : ∀ {I} -> Cons I -> (I -> Set) -> Set
⟦ ret i ⟧ B = B i
⟦ π A C ⟧ B = ∀ x -> ⟦ C x ⟧ B

-- Each `π` becomes the meta-level `Π` and the final index that a constructor receives
-- is interpreted by some provided `B`.
-- So `⟦ VCons ⟧ (Vec A)` returns the actual type of `_∷_` (modulo the implicitness of `n`):

-- `∀ n -> A -> Vec A n -> Vec A (suc n)`

-- We also need the usual way to interpret propositional/sigma descriptions ([1]/[2]):

Extendᶜ : ∀ {I} -> Cons I -> I -> Set
Extendᶜ (ret i) j = i ≡ j
Extendᶜ (π A C) j = ∃ λ x -> Extendᶜ (C x) j

-- A description of a data type is essentially a list of constructors.
-- However we allow types of constructors depend on former constructors.

Desc : (I : Set) -> (I -> Set) -> ℕ -> Set₁
Desc I B  0      = ⊤
Desc I B (suc n) = ∃ λ C -> ⟦ C ⟧ B -> Desc I B n

-- This means that when defining the type of Vec's `_∷_` you can mention Vec's `[]`.
-- It's useless for simple data types, but we'll need it for inductive-inductive ones. 

-- We're now going to define `lookup` for `Desc`. Since each description of a constructor
-- depends on all previous constructors, we need to provide these constructors somehow.
-- So here is a function that turns the described type of a constructor into actual constructor:

cons : ∀ {I B} -> (C : Cons I) -> (Extendᶜ C ∸> B) -> ⟦ C ⟧ B
cons (ret i) k = k refl
cons (π A D) k = λ x -> cons (D x) (k ∘ _,_ x)

-- It's explained in [3].

-- `cons` is able to construct a `⟦ C ⟧ B`, but it requires a `Extendᶜ C ∸> B` and since
-- `lookup i` traverses `i` constructors, we need to provide a `Extendᶜ C ∸> B` for each of them:

Nodes : ∀ {I B n} -> Fin n -> Desc I B n -> Set
Nodes          zero   (C , D) = ⊤
Nodes {B = B} (suc i) (C , D) = ∃ λ (k : Extendᶜ C ∸> B) -> Nodes i (D (cons C k))

-- `lookup` is now straightforward:

lookupᵈ : ∀ {I B n} -> (i : Fin n) -> (D : Desc I B n) -> Nodes i D -> Cons I
lookupᵈ  zero   (C , D)  tt     = C
lookupᵈ (suc i) (C , D) (k , a) = lookupᵈ i (D (cons C k)) a

-- Here is what allows to handle inductive and non-inductive occurrences uniformly:

RecDesc : Set -> ℕ -> Set₁
RecDesc I n = (B : I -> Set) -> Desc I B n

-- `μ` is defined over `R : RecDesc I n` instead of `D : Desc I B n`.
-- In the type of the constructor of `μ` `B` gets instantiated by `μ R`.
-- Thus whenever you use `B` in your description, it eventually becomes
-- replaced by an inductive occurrence. Here is a quick example:

--   Vec : Set -> ℕ -> Set
--   Vec A = μ λ B -> ret 0
--           , λ _ -> (π ℕ λ n -> π A λ _ -> π (B n) λ _ -> ret (suc n))
--           , λ _ -> tt

-- In `μ` `B` gets instantiated by `Vec A` and thus the type of the second constructor
-- is described by essentially `π ℕ λ n -> π A λ _ -> π (Vec A n) λ _ -> ret (suc n)`,
-- which we've seen above.

-- However it's not so simple to define `μ`. Consider its simplified version where
-- `μ` is defined over a three-constructors data type:

module Mu3 where
  {-# NO_POSITIVITY_CHECK #-}
  mutual
    data μ {I} (R : RecDesc I 3) j : Set where
      node : ∀ i -> Extendᶜ (lookupᵈ i (R (μ R)) (nodes i)) j -> μ R j

    nodes : ∀ {I} {R : RecDesc I 3} i -> Nodes i (R (μ R))
    nodes  zero                = tt
    nodes (suc  zero)          = node zero , tt
    nodes (suc (suc  zero))    = node zero , node (suc zero) , tt
    nodes (suc (suc (suc ())))

  -- `node` receives the number of a constructor, `lookup`s for this constructor and
  -- `Extend`s it in the usual way. However `lookupᵈ` also receives a `Nodes i (R (μ R))`,
  -- which provides `node`s for all constructors up to the `i`th
  -- (which are consumed by `cons`es in order to get actual constructors).

  -- Operationally `nodes` is trivial: it's just Data.Vec.tabulate, but returns a tuple
  -- rather than a vector, but note that the type of `node` contains multiple `node`s.
  -- This is what very/insanely dependent types are about: the ability to mention at the type level
  -- the value being defined. Check this example: [5].

  -- Agda does allow to give to constructors insanely dependent types (though, not directly),
  -- but she doesn't allow to give to functions such types. And hence we can't define:

-- nodes : ∀ {I B n} {D : Desc I B n}
--      -> (k : ∀ {j} i -> Extendᶜ (lookupᵈ i D (nodes k i)) j -> B j) -> ∀ i -> Nodes i D
-- nodes k  zero   = tt
-- nodes k (suc i) = k zero , nodes (k ∘ suc) i

-- data μ {I n} (R : RecDesc I n) j : Set where
--   node : ∀ i -> Extendᶜ (lookupᵈ i (R (μ R)) (nodes node i)) j -> μ R j

-- `nodes` receives `k` which type mentions both `nodes` and `k`.
-- Note that the type of `k` in `nodes` unifies perfectly with the type of `node`.

-- I don't know whether it's possible to circumvent the problem in some fair way,
-- but we can just cheat:

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  renodes : ∀ {I B n} {D : Desc I B n}
          -> (nodes : ∀ i -> Nodes i D)
          -> (k : ∀ {j} i -> Extendᶜ (lookupᵈ i D (nodes i)) j -> B j)
          -> ∀ i
          -> Nodes i D
  renodes         nodes k  zero   = tt
  renodes {D = D} nodes k (suc i) = k zero ,
    renodes (λ i -> subst (λ (f : Extendᶜ (proj₁ D) ∸> _) -> Nodes i (proj₂ D (cons (proj₁ D) f)))
                           trustMe
                          (proj₂ (nodes (suc i))))
            ((λ i e -> k (suc i) $
                unsubst (λ (f : _ ∸> _) y -> Extendᶜ (lookupᵈ i (proj₂ D (cons _ f)) y) _)
                         trustMe
                         e))
             i

  -- `renodes` has the same computational content as `nodes`, but it assumes that `nodes`
  -- is already defined (because we need to use it at the type level) and
  -- essentially "redefines" it (because we need to compute something eventually).
  -- The ability to compute at the type level for `nodes` is given by
  -- `trustMe`, `subst` and `unsubst`.

-- And here is where we actually tie the knot:

{-# NO_POSITIVITY_CHECK #-}
{-# TERMINATING #-}
mutual
  data μ {I n} (R : RecDesc I n) j : Set where
    node : ∀ i -> Extendᶜ (lookupᵈ i (R (μ R)) (nodes i)) j -> μ R j

  nodes : ∀ {I n} {R : RecDesc I n} i -> Nodes i (R (μ R))
  nodes zero = tt -- This is in order to prevent infinite unfolding of `nodes`.
  nodes i    = renodes nodes node i

-- Some shortcuts:

_⇒_ : ∀ {I} -> Set -> Cons I -> Cons I
A ⇒ C = π A λ _ -> C

RecDesc′ : ℕ -> Set₁
RecDesc′ n = (B : Set) -> Desc ⊤ (const B) n

μ′ : ∀ {n} -> RecDesc′ n -> Set 
μ′ R = μ (λ B -> R (B tt)) tt

pattern #₀ p = node  zero                        p
pattern #₁ p = node (suc  zero)                  p
pattern #₂ p = node (suc (suc  zero))            p
pattern #₃ p = node (suc (suc (suc  zero)))      p
pattern #₄ p = node (suc (suc (suc (suc zero)))) p

pattern ⟨⟩₁ = node (suc  ())                        _
pattern ⟨⟩₂ = node (suc (suc  ()))                  _
pattern ⟨⟩₃ = node (suc (suc (suc  ())))            _
pattern ⟨⟩₄ = node (suc (suc (suc (suc  ()))))      _
pattern ⟨⟩₅ = node (suc (suc (suc (suc (suc ()))))) _

-- It's not needed to explicitly refute last clauses using `⟨⟩ᵢ`,
-- when `Fin` is defined computationally like this:

-- Fin : ℕ -> Set
-- Fin  0      = ⊥
-- Fin  1      = ⊤
-- Fin (suc n) = Maybe (Fin n)

-- but it's a bit inconvenient to use such `Fin`s.

-- The described dependently typed hello-world:

module Simple where
  data Vec (A : Set) : ℕ -> Set where
    []  : Vec A 0
    _∷_ : ∀ {n} -> A -> Vec A n -> Vec A (suc n)

  Vec′ : Set -> ℕ -> Set
  Vec′ A = μ λ Vec′A -> ret 0
           , λ _     -> (π ℕ λ n -> A ⇒ Vec′A n ⇒ ret (suc n))
           , λ _     -> tt

  pattern []′           = #₀  refl
  pattern _∷′_ {n} x xs = #₁ (n , x , xs , refl)

  Vec→Vec′ : ∀ {A n} -> Vec A n -> Vec′ A n
  Vec→Vec′  []      = []′
  Vec→Vec′ (x ∷ xs) = x ∷′ Vec→Vec′ xs

  Vec′→Vec : ∀ {A n} -> Vec′ A n -> Vec A n
  Vec′→Vec  []′      = []
  Vec′→Vec (x ∷′ xs) = x ∷ Vec′→Vec xs
  Vec′→Vec  ⟨⟩₂

  -- This all is entirely standard except that the inductive occurrence in the type of
  -- the second constructor is `Vec′A n` rather than `var n` or something similar.

-- We can describe strictly positive data types which are not so easy to
-- handle with usual descriptions. `Rose` e.g. is

module Positive where
  open import Data.List.Base

  data Rose (A : Set) : Set where
    rose : A -> List (Rose A) -> Rose A

  Rose′ : Set -> Set
  Rose′ A = μ′ λ Rose′A -> (A ⇒ List Rose′A ⇒ ret tt)
               , λ _    -> tt

  pattern rose′ x rs = #₀ (x , rs , refl)

  {-# TERMINATING #-} -- I refuse to manually inline `map`.
  Rose→Rose′ : ∀ {A} -> Rose A -> Rose′ A
  Rose→Rose′ (rose x rs) = rose′ x (map Rose→Rose′ rs)

  {-# TERMINATING #-}
  Rose′→Rose : ∀ {A} -> Rose′ A -> Rose A
  Rose′→Rose (rose′ x rs) = rose x (map Rose′→Rose rs)
  Rose′→Rose  ⟨⟩₁

  -- In order to describe `Rose` in a safe-by-design way you need a rather complicated
  -- machinery of indexed functors with multiple internal fixpoints ([6]) and
  -- `List` must be described as well.

-- But we can also describe non-strictly positive data types. Here is some HOAS:

module NonPositive where
  data Type : Set where
    ι   : Type
    _⇨_ : Type -> Type -> Type

  {-# NO_POSITIVITY_CHECK #-}
  data Term : Type -> Set where
    lam : ∀ {σ τ} -> (Term σ -> Term τ) -> Term (σ ⇨ τ)
    app : ∀ {σ τ} -> Term (σ ⇨ τ) -> Term σ -> Term τ

  Term′ : Type -> Set
  Term′ = μ λ Term′ -> (π _ λ σ -> π _ λ τ -> (Term′ σ -> Term′ τ) ⇒ ret (σ ⇨ τ))
          , λ _     -> (π _ λ σ -> π _ λ τ -> Term′ (σ ⇨ τ) ⇒ Term′ σ ⇒ ret τ)
          , λ _     -> tt

  pattern lam′ k   = #₀ (_ , _ , k     , refl) 
  pattern app′ f x = #₁ (_ , _ , f , x , refl)

  {-# TERMINATING #-}
  mutual
    Term→Term′ : ∀ {σ} -> Term σ -> Term′ σ
    Term→Term′ (lam k)   = lam′ λ x -> Term→Term′ (k (Term′→Term x))
    Term→Term′ (app f x) = app′ (Term→Term′ f) (Term→Term′ x)

    Term′→Term : ∀ {σ} -> Term′ σ -> Term σ
    Term′→Term (lam′ k)   = lam λ x -> Term′→Term (k (Term→Term′ x))
    Term′→Term (app′ f x) = app (Term′→Term f) (Term′→Term x)
    Term′→Term  ⟨⟩₂

-- And the final example: a described inductive-inductive data type:

module InductiveInductive where
  infix 4 _∉_ _∉′_

  -- a `UList A` is a list, all elements of which are distinct.
  mutual
    data UList (A : Set) : Set where
      []    : UList A
      ucons : ∀ {x xs} -> x ∉ xs -> UList A

    data _∉_ {A} (x : A) : UList A -> Set where
      stop : x ∉ []
      keep : ∀ {y xs} -> x ≢ y -> (p : y ∉ xs) -> x ∉ xs -> x ∉ ucons p

  -- In order to describe these data types we introduce the type of `Tag`s:

  data Tag (A : Set) : Set₁ where
    ulist : Tag A
    inn   : {R : Set} -> A -> R -> Tag A

  -- So we define `UListInn′` which is indexed by a `Tag A` and
  -- describes both `UList` (the `ulist` tag) and `_∉_` (the `inn` tag).
  -- Described `UList` is just `UList′ A = UListInn′ (ulist {A})`. `_∉′_` is similar.

  -- The `inn` tag allows to instantiate `R` with anything,
  -- but we always instantiate it with `UList A` in the constructors of `UListInn′`.

  -- Without descriptions it looks like this:

  module NoDesc where
    {-# NO_POSITIVITY_CHECK #-}
    data UListInn′ (A : Set) : Tag A -> Set where
      []′    : UListInn′ A ulist
      ucons′ : ∀ {x} {xs : UListInn′ A ulist} -> UListInn′ A (inn x xs) -> UListInn′ A ulist
      stop′  : ∀ {x} -> UListInn′ A (inn x (UListInn′ A ulist ∋ []′))
      keep′  : ∀ {x y} {xs : UListInn′ A ulist}
             -> x ≢ y
             -> (p : UListInn′ A (inn y xs))
             -> UListInn′ A (inn x xs)
             -> UListInn′ A (inn x (ucons′ p))

  -- And the direct encoding of the above data type is

  UListInn′ : ∀ {A} -> Tag A -> Set
  UListInn′ {A} =
    μ λ UListInn′ -> ret ulist
    , λ []′       -> (π A λ x -> π (UListInn′ ulist) λ xs -> UListInn′ (inn x xs) ⇒ ret ulist)
    , λ ucons′    -> (π A λ x -> ret (inn x []′))
    , λ _         -> (π A λ x -> π A λ y -> π (UListInn′ ulist) λ xs -> x ≢ y ⇒
                        π (UListInn′ (inn y xs)) λ p -> UListInn′ (inn x xs) ⇒
                          ret (inn x (ucons′ y xs p)))
    , λ _         -> tt

  -- Note that we use the constructors of `UListInn′` (`[]′` and `ucons′`) in the definition of
  -- `UListInn′`.

  -- `--type-in-type` is needed, because `Tag A` is too big and lies in `Set₁`,
  -- but the actual `UList′ A` and `x ∉′ xs` are in `Set` like they should:

  UList′ : Set -> Set
  UList′ A = UListInn′ (ulist {A})

  _∉′_ : ∀ {A} -> A -> UList′ A -> Set
  x ∉′ xs = UListInn′ (inn x xs)

  pattern []′                      = #₀  refl
  pattern ucons′ {x} {xs} p        = #₁ (x , xs , p , refl)
  pattern stop′ {x}                = #₂ (x , refl)
  pattern keep′ {x} {y} {xs} c p q = #₃ (x , y , xs , c , p , q , refl)

  -- The final test:

  mutual
    UList→UList′ : ∀ {α} {A : Set α} -> UList A -> UList′ A
    UList→UList′  []       = []′
    UList→UList′ (ucons p) = ucons′ (Inn→Inn′ p)

    Inn→Inn′ : ∀ {α} {A : Set α} {x : A} {xs} -> x ∉ xs -> x ∉′ UList→UList′ xs
    Inn→Inn′  stop        = stop′
    Inn→Inn′ (keep c p q) = keep′ c (Inn→Inn′ p) (Inn→Inn′ q)

  mutual
    UList′→UList : ∀ {α} {A : Set α} -> UList′ A -> UList A
    UList′→UList  []′       = []
    UList′→UList (ucons′ p) = ucons (Inn′→Inn p)
    UList′→UList (#₂ (_ , ()))
    UList′→UList (#₃ (_ , _ , _ , _ , _ , _ , ()))
    UList′→UList  ⟨⟩₄

    Inn′→Inn : ∀ {α} {A : Set α} {x : A} {xs} -> x ∉′ xs -> x ∉ UList′→UList xs
    Inn′→Inn  stop′        = stop
    Inn′→Inn (keep′ c p q) = keep c (Inn′→Inn p) (Inn′→Inn q)
    Inn′→Inn (#₀ ())
    Inn′→Inn (#₁ (_ , _ , _ , ()))
    Inn′→Inn  ⟨⟩₄

module References where
  -- [1] "Modeling Elimination of Described Types", Larry Diehl
  -- http://spire-lang.org/blog/2014/01/15/modeling-elimination-of-described-types/

  -- [2] "Generic programming with ornaments and dependent types", Yorick Sijsling
  -- http://sijsling.com/files/Thesis-YorickSijsling-color.pdf

  -- [3] "Deriving eliminators of described data types"
  -- http://effectfully.blogspot.com/2016/06/deriving-eliminators-of-described-data.html

  -- [4] https://github.com/effectfully/Generic/blob/master/Examples/Experiment.agda

  -- [5] "Toy typechecker for Insanely Dependent Types", Ulf Norell
  -- https://github.com/UlfNorell/insane/blob/694d5dcfdc3d4dd4f31138228ef8d87dd84fa9ec/Sigma.agda#L15

  -- [6] "Generic Programming with Indexed Functors", Andres Löh, José Pedro Magalhães
  -- http://dreixel.net/research/pdf/gpif.pdf
