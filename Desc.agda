-- In this post I'll shortly introduce descriptions and describe a variant of them that I prefer.
-- If you haven't seen this form of generic programming before,
-- you might want to start with something simpler first:
-- http://effectfully.blogspot.com/2016/02/simple-generic-programming.html

{-# OPTIONS --type-in-type --no-termination-check #-}

module Desc where

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product

module Computational where
  -- I'll start by defining descriptions in their usual computational form.

  data Desc I : Set where
    ind : I -> Desc I
    κ   : Set -> Desc I
    σ π : ∀ A -> (A -> Desc I) -> Desc I
    _⊛_ : Desc I -> Desc I -> Desc I

  ⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
  ⟦ ind i ⟧ F = F i
  ⟦ κ A   ⟧ F = A
  ⟦ σ A B ⟧ F = Σ A λ x -> ⟦ B x ⟧ F
  ⟦ π A B ⟧ F = (x : A) -> ⟦ B x ⟧ F
  ⟦ D ⊛ E ⟧ F = ⟦ D ⟧ F × ⟦ E ⟧ F

  record μ {I} (F : I -> Desc I) j : Set where
    inductive
    constructor node
    field knot : ⟦ F j ⟧ (μ F)

  -- `ind i` is an inductive position. `⟦ ind i ⟧ (μ F)` reduces to `μ F i`,
  -- so that is where knot tying happens. In `μ F j` `j` is the index of a term
  -- and in `ind i` `i` is the index of a subterm.

  -- `κ` allows to embed any `Set` into a description.
  -- `σ` allows this too, but `κ` is non-recursive and thus can finish a description.

  -- `σ` serves two purposes:
  --   1. It allows to split a description of a data type into descriptions of several constructors.
  --      E.g. we can express the fact that a data type has two constructors by defining its
  --      description as `σ Bool λ b -> if b then cons₁ else cons₂` for some `cons₁` and `cons₂`.
  --   2. It encodes top-level Π-types in the type of a constructor in a target language.
  --      I'll explain in a minute why we use `σ` to encode `Π`.
  
  -- `π` is for higher-order inductive occurrences. I.e. for data types where an inductive
  -- position appears to the right of the arrow. E.g. `W`:

  -- data W (A : Set) (B : A -> Set) : Set where
  --   sup : (x : A) -> (B x -> W A B) -> W A B

  -- or `Desc` itself (the `σ` and `π`) constructors.

  -- `D ⊛ E` is a first-order equivalent of `π Bool λ b -> if b then D else E`.

  -- The choice operator mentioned above:

  _⊕_ : ∀ {I} -> Desc I -> Desc I -> Desc I
  D ⊕ E = σ Bool λ b -> if b then D else E

  -- Here is an example of described data type.

  list : Set -> Desc ⊤
  list A = κ ⊤
         ⊕ σ A λ _ -> ind tt
  
  List : Set -> Set
  List A = μ (λ _ -> list A) tt

  -- Lists are a non-indexed data type, hence we pass `⊤` to `Desc`, and
  -- lists have two constructors: the one that doesn't contain any data
  -- (which is expressed as `κ ⊤`) and the other that contains an `A` and an inductive occurrence.

  -- The recovered constructors:

  -- [] : ∀ {A} -> List A
  pattern [] = node (true , tt)

  -- _∷_ : ∀ {A} -> A -> List A -> List A
  pattern _∷_ x xs = node (false , x , xs)

  -- Now we can see why `σ` is used to describe the arguments to a constructor.
  -- If we define `List` via the `data` keyword, then `_∷_` is a "god-given" function,
  -- but internally it's just a tag "cons" stored among with an element and a sublist.
  -- Here we store the element and the sublist explicitly.

  -- You can read described constructors like there is `-> D` after them,
  -- where `D` is the data type being described. E.g. for the usual lists `_∷_` can be defined as
  
  -- `cons : (A × List A) -> List A`

  -- which is the same as

  -- `cons : (Σ A λ _ -> List A) -> List A`.
  
  -- compare this to `_∷_` described above: `σ A λ _ -> ind tt`.

  -- Described lists have the usual eliminator.

  elimList : ∀ {A}
           -> (P : List A -> Set)
           -> (∀ {xs} x -> P xs -> P (x ∷ xs))
           -> P []
           -> ∀ xs
           -> P xs
  elimList P f z  []      = z
  elimList P f z (x ∷ xs) = f x (elimList P f z xs)

  -- Now let's describe something indexed.

  fin : ℕ -> Desc ℕ
  fin n = (σ ℕ λ m -> κ (n ≡ suc m))
        ⊕ (σ ℕ λ m -> σ (n ≡ suc m) λ _ -> ind m)

  Fin : ℕ -> Set
  Fin = μ fin

  -- fzero : ∀ {n} -> Fin (suc n)
  pattern fzero {n} = node (true , n , refl)

  -- fsuc : ∀ {n} -> Fin n -> Fin (suc n)
  pattern fsuc {n} i = node (false , n , refl , i)

  -- `Fin` has two constructors and in order to describe them we must introduce explicit
  -- unification constraints. `Fin n` is inhabited only when `n ≡ suc m` for some `m` --
  -- that's what the description says. Since the unification constraint is the same for
  -- both constructors, we could introduce it before defining actual constructors:

  module Before where
    fin′ : ℕ -> Desc ℕ
    fin′ n = σ ℕ λ m -> σ (n ≡ suc m) λ _ -> κ ⊤ ⊕ ind m

    Fin′ : ℕ -> Set
    Fin′ = μ fin′

    fzero′ : ∀ {n} -> Fin′ (suc n)
    fzero′ {n} = node (n , refl , true , tt)

    fsuc′ : ∀ {n} -> Fin′ n -> Fin′ (suc n)
    fsuc′ {n} i = node (n , refl , false , i)

  -- `Fin` has the usual induction principle:

  elimFin : ∀ {n}
          -> (P : ∀ {n} -> Fin n -> Set)
          -> (∀ {n} {i : Fin n} -> P i -> P (fsuc i))
          -> (∀ {n} -> P (fzero {n}))
          -> (i : Fin n)
          -> P i
  elimFin P f x  fzero   = x
  elimFin P f x (fsuc i) = f (elimFin P f x i)

  -- But these explicit unification constraints are quite ugly.
  -- Moreover, sometimes you want to have access to them while defining generic functions
  -- over `Desc`, but constraints can appear everywhere in the definition of a description,
  -- so you can't locate them by just pattern matching on a `Desc`.

module Propositional where
  -- So here are propositional descriptions that solve most of the problems mentioned above.
  -- I'm taking stuff directly from [1].

  data Desc I : Set where
    ret  : I -> Desc I
    σ    : ∀ A -> (A -> Desc I) -> Desc I
    ind  : I -> Desc I -> Desc I
    hind : ∀ A -> (A -> I) -> Desc I -> Desc I

  Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
  Extend (ret i)      F j = j ≡ i
  Extend (σ A B)      F j = Σ A λ x -> Extend (B x) F j
  Extend (ind i D)    F j = F i × Extend D F j
  Extend (hind A k D) F j = ((x : A) -> F (k x)) × Extend D F j

  record μ {I} (D : Desc I) j : Set where
    inductive
    constructor node
    field knot : Extend D (μ D) j

  -- Each desciption ends with `ret` that receives the index of a term.
  -- `σ` is the same thing as before.
  -- `ind` carries an inductive position and the rest of a description.
  -- `hind` is the same thing as `ind`, but an inductive occurrence is higher-order.

  -- `Extend` is straightforward and pretty linear. The only interesting case is `ret`:
  -- that's where we put constraints. Now we don't need to write them down explicitly.

  -- However I don't like the `(A -> I)` part in `hind`. If we want to encode something like

  data Foo : Set where
    foo : (ℕ -> Bool -> Foo) -> Foo

  -- then `A` must be `ℕ × Bool` and this compulsory uncurrying is annoying.
  -- Manual extraction of elements from a big tuple is verbose and ugly.

  -- To encode this definition

  data Bar : Set where
    foo : (ℕ -> Bar × Bar) -> Bar

  -- we have to transform it to

  data Bar′ : Set where
    foo : (ℕ -> Bar′) -> (ℕ -> Bar′) -> Bar′

  -- Computational descriptions didn't have these problems.

module CompProp where
  infixr 6 _⊛_
  infixr 5 _⊕_
  
  -- So here is a compact and convenient form of descriptions:

  data Desc I : Set where
    var : I -> Desc I
    π   : ∀ A -> (A -> Desc I) -> Desc I
    _⊛_ : Desc I -> Desc I -> Desc I

  ⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
  ⟦ var i ⟧ F = F i
  ⟦ π A B ⟧ F = ∀ x -> ⟦ B x ⟧ F
  ⟦ D ⊛ E ⟧ F = ⟦ D ⟧ F × ⟦ E ⟧ F

  Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
  Extend (var j) F i = j ≡ i
  Extend (π A B) F i = ∃ λ x -> Extend (B x) F i
  Extend (D ⊛ E) F i = ⟦ D ⟧ F × Extend E F i

  record μ {I} (D : Desc I) i : Set where
    inductive
    constructor node
    field knot : Extend D (μ D) i

  -- `⟦_⟧` is taken from computational descriptions and
  -- `Extend` is taken from propositional descriptions.

  -- `var` serves as both `ind` and `ret`. There is `var i` at the end of each constructor,
  -- where `i` is the index that a constructor returns. All other `var`s in a description
  -- represent inductive positions.

  -- `π` subsumes both `σ` and `π` from computation descriptions.
  -- `Extend` interprets `π` as `∃` and `⟦_⟧` interprets `π` as `Π`.

  -- Note that `μ` in this representation and in the propositional one receives a proper
  -- first-order `Desc`, while in the computational representation `μ` receives a
  -- higher-order `I -> Desc I`.

  _⊕_ : ∀ {I} -> Desc I -> Desc I -> Desc I
  D ⊕ E = π Bool λ b -> if b then D else E

  -- Everything should become clear after looking at an example:

  vec : Set -> Desc ℕ
  vec A = var 0
        ⊕ π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)

  Vec : Set -> ℕ -> Set
  Vec A = μ (vec A)

  -- Vectors have two constructors: the one that doesn't contain any data and
  -- the other that carries an `A` and a subvector `xs : Vec A n`.
  -- The former constructor returns a vector of length `0` and
  -- the latter returns a vector of length `suc n`.
  -- Compare this to the usual definition of vectors which has the same pattern:

  module UsualVec where
    data Vec′ (A : Set) : ℕ -> Set where
      []  : Vec′ A 0
      _∷_ : ∀ {n} -> A -> Vec′ A n -> Vec′ A (suc n)

  -- `Extend` interprets `π` as `∃`, i.e. like `⟦_⟧` in computational descriptions interprets `σ`,
  -- so the recovered constructors are very similar:

  -- [] : ∀ {A} -> Vec A 0
  pattern [] = node (true , refl)

  -- _∷_ : ∀ {n A} -> A -> Vec A n -> Vec A (suc n)
  pattern _∷_ {n} x xs = node (false , n , x , xs , refl)

  elimVec : ∀ {n A}
          -> (P : ∀ {n} -> Vec A n -> Set)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ xs))
          -> P []
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z  []      = z
  elimVec P f z (x ∷ xs) = f x (elimVec P f z xs)

  -- Let's now encode `W`:

  w : ∀ A -> (A -> Set) -> Desc ⊤
  w A B = π A λ x -> (π (B x) λ _ -> var tt) ⊛ var tt

  W : ∀ A -> (A -> Set) -> Set
  W A B = μ (w A B) tt

  -- sup : ∀ {A B} -> (x : A) -> (B x -> W A B) -> W A B
  pattern sup x g = node (x , g , refl)

  -- The key thing here is that `Extend` interprets `D` and `E` in `D ⊛ E` differently.
  -- In `D` `π` encodes actual `Π` and `var i` is an inductive position.
  -- In `E` `π` encodes `∃` and `var i` (if it's not to the left of another `_⊛_`)
  -- represents the index that a constructor returns.

  -- Compare this to the usual definion of `W`:

  module UsualW where
    data W′ A (B : A -> Set) : Set where
      sup′ : (x : A) -> (B x -> W′ A B) -> W′ A B

  -- They are quite the same except that `_⊛_` is replaced by `_->_`.

  -- As the final example we can encode `Desc` itself:

  data Codes : Set where
    varᶜ πᶜ ⊛ᶜ : Codes

  desc : Set -> Desc ⊤
  desc I = π Codes λ
    { varᶜ -> π I λ _ -> var tt
    ; πᶜ   -> π Set λ A -> (π A λ _ -> var tt) ⊛ var tt
    ; ⊛ᶜ   -> var tt ⊛ var tt ⊛ var tt
    }

  Desc′ : Set -> Set
  Desc′ I = μ (desc I) tt

  -- var′ : ∀ {I} -> I -> Desc′ I
  pattern var′ i = node (varᶜ , i , refl)

  -- π′ : ∀ {I} A -> (A -> Desc′ I) -> Desc′ I
  pattern π′ A B = node (πᶜ , A , B , refl)

  -- _⊛′_ : ∀ {I} -> Desc′ I -> Desc′ I -> Desc′ I
  pattern _⊛′_ D E = node (⊛ᶜ , D , E , refl)

  -- `Desc` and `Desc′` are clearly isomorphic:

  fromDesc : ∀ {I} -> Desc I -> Desc′ I
  fromDesc (var i) = var′ i
  fromDesc (π A B) = π′ A λ x -> fromDesc (B x)
  fromDesc (D ⊛ E) = fromDesc D ⊛′ fromDesc E

  toDesc : ∀ {I} -> Desc′ I -> Desc I
  toDesc (var′ i) = var i
  toDesc (π′ A B) = π A λ x -> toDesc (B x)
  toDesc (D ⊛′ E) = toDesc D ⊛ toDesc E

module References where
  -- [1] "Modeling Elimination of Described Types"
  -- Larry Diehl
  -- http://spire-lang.org/blog/2014/01/15/modeling-elimination-of-described-types/
