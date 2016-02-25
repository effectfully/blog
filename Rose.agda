-- When I was reading about descriptions ([1]), I was wondering whether
-- there is an encoding that is not that powerful, but simple, straightforward
-- and allows to encode a vast amount of data types among with their elimination principles
-- (the containers approach ([2]) doesn't allow this in an intensional type theory [3]).
-- I'll describe such encoding.

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
open import Data.List.Base

infixr 5 _∷₁_

-- `List₁ B xs` contains a `B x` for each `x` in `xs`.
-- It's the same `All` from `Data.List.All`, but lies in `Set β` rather than `Set (α ⊔ β)`.

data List₁ {α β} {A : Set α} (B : A -> Set β) : List A -> Set β where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

-- And here is the encoding.

Over : ∀ {ι} -> Set ι -> ∀ α -> Set (ι ⊔ lsuc α)
Over I α = List I -> I -> Set α

record Rose {ι α} {I : Set ι} (F : Over I α) j : Set (ι ⊔ α) where
  inductive
  constructor node
  field
    {is}   : List I
    cons   : F is j
    childs : List₁ (Rose F) is

-- `Over` describes all possible constructors of a data type and
-- `Rose` ties the knot and connects these constructors together.

-- `Rose` is able to express inductive families and that's why there is the `I` --
-- it's the type of the indices of a data type.

-- `Over` contains all information about a data type being described
-- except for inductive occurrences, which are reflected to the type level
-- by storing their indices in `List I`. The final `I` in

-- Over I α = List I -> I -> Set α

-- is for the index that a constructor produces.

-- Here is how it looks for vectors:
module Vec where
  data VecF {α} (A : Set α) : Over ℕ α where

    -- The first constructor for `Vec` (`[]ᵥ`) doesn't contain any data
    -- and it produces the index `0`.
    Nil  : VecF A [] 0
  
    -- The second constructor for `Vec` (`_∷ᵥ_`) contains an `A` and
    -- an inductive occurrence of `Vec`. It produces the index `suc n`
    -- where `n` is the index of the inductive occurrence.
    -- Hence we put `n` into the list of indices of inductive occurrences and return `suc n`.
    Cons : ∀ {n} -> A -> VecF A (n ∷ []) (suc n)

  -- `Vec` then is
  
  Vec : ∀ {α} -> Set α -> ℕ -> Set α
  Vec A n = Rose (VecF A) n

  -- Let's look again at the definition of `Rose`:

  -- record Rose {ι α} {I : Set ι} (F : Over I α) j : Set (ι ⊔ α) where
  --   inductive
  --   constructor node
  --   field
  --     {is}   : List I
  --     cons   : F is j
  --     childs : List₁ (Rose F) is

  -- `j` is an index of an inhabitant of a data type.
  -- `is` is a list of indices of inductive occurrences.
  -- `cons` is a constructor of this data type.
  -- `childs` is a list of `Rose F i` for each `i` in `is`,
  -- i.e. a list that actually contains inductive occurrences (finally).

  -- Recall the definition of `Cons`:
  
  -- `Cons : ∀ {n} -> A -> VecF A (n ∷ []) (suc n)`
  
  -- When we write `node (Cons x)` `is` gets unified with `_n ∷ []` and
  -- `j` gets unified with `suc _n` for a fresh meta `_n`.
  -- Thus, `childs` has type `List₁ (Vec A) (_n ∷ [])`,
  -- i.e. there is exactly one child -- `Vec A n`.

  -- So here are the constructors:

  -- []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
  -- []ᵥ = node Nil []₁

  -- _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
  -- x ∷ᵥ xs = node (Cons x) (xs ∷₁ []₁)

  -- But for convenience we'll define them as pattern synonyms instead

  pattern []ᵥ = node Nil []₁
  pattern _∷ᵥ_ x xs = node (Cons x) (xs ∷₁ []₁)

  -- And guess what, we have literally the same eliminator as for the usual `Vec`:

  elimVec : ∀ {α π} {A : Set α} {n}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
          -> P []ᵥ
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z  []ᵥ      = z
  elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)

  -- So we basically don't need it -- we can use pattern matching directly, e.g.:

  vmap : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> Vec A n -> Vec B n
  vmap f  []ᵥ      = []ᵥ
  vmap f (x ∷ᵥ xs) = f x ∷ᵥ vmap f xs

  vhead : ∀ {n α} {A : Set α} -> Vec A (suc n) -> A
  vhead (x ∷ᵥ xs) = x

module AnEliminator where
  -- We can of course define an eliminator of `Rose`.
  -- But let's define an eliminator for something simpler first.

  data Tree {α} (A : Set α) : Set α where
    branch : A -> List (Tree A) -> Tree A

  -- An eliminator is an induction principle and an induction hypothesis
  -- sounds like "`P` holds, if it holds at every inductive position".
  -- To say "`P` holds for a list `xs` of inductive occurrences" we write `List₁ P xs`.
  -- Here is the eliminator:

  elimTree : ∀ {α π} {A : Set α}
           -> (P : Tree A -> Set π)
           -> (∀ {ts} x -> List₁ P ts -> P (branch x ts))
           -> ∀ t
           -> P t
  elimTree P f (branch x ts) = f x (elimTrees ts) where
    elimTrees : ∀ ts -> List₁ P ts
    elimTrees  []      = []₁
    elimTrees (t ∷ ts) = elimTree P f t ∷₁ elimTrees ts

  -- `Rose` is basically the same thing as `Tree`, but there is `List₁` instead of `List`.
  -- All we need is to define `List₂` over `List₁` in the same manner as `List₁` over `List` before.

  data List₂ {α β γ} {A : Set α} {B : A -> Set β} (C : ∀ {x} -> B x -> Set γ)
             : ∀ {xs} -> List₁ B xs -> Set γ where
    []₂  : List₂ C []₁
    _∷₂_ : ∀ {x xs} {y : B x} {ys : List₁ B xs} -> C y -> List₂ C ys -> List₂ C (y ∷₁ ys)
  
  lmap₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ} {xs}
        -> (∀ {x} -> (y : B x) -> C y) -> (ys : List₁ B xs) -> List₂ C ys
  lmap₂ g  []₁      = []₂
  lmap₂ g (y ∷₁ ys) = g y ∷₂ lmap₂ g ys

  {-# TERMINATING #-}
  elimRose : ∀ {ι α π} {I : Set ι} {F : Over I α} {j}
           -> (P : ∀ {j} -> Rose F j -> Set π)
           -> (∀ {is j cs} -> (c : F is j) -> List₂ P cs -> P (node c cs))
           -> (r : Rose F j)
           -> P r
  elimRose P f (node c cs) = f c (lmap₂ (elimRose P f) cs)

  -- We could get rid of the `{-# TERMINATING #-}` pragma by inlining `lmap₂' and
  -- defining `elimRose` mutually with `elimRoses` as in the case of `Tree`, but I hate this.

  -- As an example, let's define an eliminator for `Vec` in terms of `elimRose`.

  open Vec

  elimVec′ : ∀ {α π} {A : Set α} {n}
           -> (P : ∀ {n} -> Vec A n -> Set π)
           -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
           -> P []ᵥ
           -> (xs : Vec A n)
           -> P xs
  elimVec′ {A = A} P f z = elimRose P h where
    h : ∀ {is j cs} -> (c : VecF A is j) -> List₂ P cs -> P (node c cs) 
    h  Nil      []₂        = z
    h (Cons x) (xs ∷₂ []₂) = f x xs

  -- Not super nice, but works.

  -- A recursor is similar:

  unmap₁ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {xs}
         -> (∀ {x} -> B x -> C) -> List₁ B xs -> List C
  unmap₁ g  []₁      = []
  unmap₁ g (y ∷₁ ys) = g y ∷ unmap₁ g ys

  {-# TERMINATING #-}
  foldRose : ∀ {ι α π} {I : Set ι} {F : Over I α} {j} {P : Set π}
           -> (∀ {is j} -> F is j -> List P -> P) -> Rose F j -> P
  foldRose f (node c cs) = f c (unmap₁ (foldRose f) cs)

  -- We can define a generic `depth` function that returns the depth of any `Rose`.

  depth : ∀ {ι α} {I : Set ι} {F : Over I α} {j} -> Rose F j -> ℕ
  depth = foldRose (λ _ -> foldr (_⊔ℕ_ ∘ suc) 0)

  -- A simple test:

  vec-depth : ∀ {n α} {A : Set α} -> (xs : Vec A n) -> depth xs ≡ n
  vec-depth  []ᵥ      = refl
  vec-depth (x ∷ᵥ xs) = cong suc (vec-depth xs)

-- One restriction is that we can't describe data types in which an inductive position occurs
-- to the right of the arrow in a parameter of a constructor (like e.g. in `W`).
-- This is fixable: I wrote a library that deals with Observational Type Theory,
-- `W` is expressible there and has the usual induction principle.
-- Here it is: https://github.com/effectfully/OTT/blob/master/Data/W.agda

-- An extended example: simply typed lambda calculus.
module STLC where
  infixr 6 _⇒_
  infixl 5 _▻_
  infix  3 _∈_ _⊢_
  infixr 4 vs_
  infixr 0 ƛ_
  infixl 6 _·_

  data Type : Set where
    nat : Type
    _⇒_ : Type -> Type -> Type

  ⟦_⟧ : Type -> Set
  ⟦ nat   ⟧ = ℕ
  ⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

  data Con : Set where
    ε   : Con
    _▻_ : Con -> Type -> Con

  data _∈_ σ : Con -> Set where
    vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
    vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

  data Env : Con -> Set where
    ∅   : Env ε
    _▷_ : ∀ {Γ σ} -> Env Γ -> ⟦ σ ⟧ -> Env (Γ ▻ σ)

  lookupᵉ : ∀ {Γ σ} -> σ ∈ Γ -> Env Γ -> ⟦ σ ⟧
  lookupᵉ  vz    (ρ ▷ x) = x
  lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

  data TermF : Over (Con × Type) lzero where
    Pure  : ∀ {Γ σ  } -> ⟦ σ ⟧ -> TermF  []                                      (Γ , σ    )
    Var   : ∀ {Γ σ  } -> σ ∈ Γ -> TermF  []                                      (Γ , σ    )
    Lam   : ∀ {Γ σ τ} ->          TermF ((Γ ▻ σ , τ) ∷ [])                       (Γ , σ ⇒ τ)
    App   : ∀ {Γ σ τ} ->          TermF ((Γ , σ ⇒ τ) ∷ (Γ , σ) ∷ [])             (Γ , τ    )
    Z     : ∀ {Γ    } ->          TermF  []                                      (Γ , nat  )
    S     : ∀ {Γ    } ->          TermF ((Γ , nat) ∷ [])                         (Γ , nat  )
    Fold  : ∀ {Γ σ  } ->          TermF ((Γ , σ ⇒ σ) ∷ (Γ , σ) ∷ (Γ , nat) ∷ []) (Γ , σ    )
  
  _⊢_ : Con -> Type -> Set
  Γ ⊢ σ = Rose TermF (Γ , σ)

  Term⁺ : Type -> Set
  Term⁺ σ = ∀ {Γ} -> Γ ⊢ σ

  Term⁽⁾ : Type -> Set
  Term⁽⁾ σ = ε ⊢ σ

  pattern pure x      = node (Pure x) []₁
  pattern var v       = node (Var v) []₁
  pattern ƛ_ b        = node Lam (b ∷₁ []₁)
  pattern _·_ f x     = node App (f ∷₁ x ∷₁ []₁)
  pattern z           = node Z []₁
  pattern s n         = node S (n ∷₁ []₁)
  pattern tfold f x n = node Fold (f ∷₁ x ∷₁ n ∷₁ []₁)

  ⟦_⟧ᵥ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧
  ⟦ pure x      ⟧ᵥ ρ = x
  ⟦ var v       ⟧ᵥ ρ = lookupᵉ v ρ
  ⟦ ƛ b         ⟧ᵥ ρ = λ x -> ⟦ b ⟧ᵥ (ρ ▷ x)
  ⟦ f · x       ⟧ᵥ ρ = ⟦ f ⟧ᵥ ρ (⟦ x ⟧ᵥ ρ)
  ⟦ z           ⟧ᵥ ρ = 0
  ⟦ s n         ⟧ᵥ ρ = suc (⟦ n ⟧ᵥ ρ)
  ⟦ tfold f x n ⟧ᵥ ρ = fold (⟦ x ⟧ᵥ ρ) (⟦ f ⟧ᵥ ρ) (⟦ n ⟧ᵥ ρ)

  eval : ∀ {σ} -> Term⁽⁾ σ -> ⟦ σ ⟧
  eval t = ⟦ t ⟧ᵥ ∅

  A : ∀ {σ τ} -> Term⁺ ((σ ⇒ τ) ⇒ σ ⇒ τ)
  A = ƛ ƛ var (vs vz) · var vz

  test : ∀ {σ τ} -> eval (A {σ} {τ}) ≡ _$_
  test = refl

module References where
  -- [1] "The Gentle Art of Levitation"
  -- James Chapman, Pierre-Evariste Dagand, Conor McBride, Peter Morris
  -- http://jmchapman.github.io/papers/levitation.pdf
  
  -- [2] "Indexed Containers"
  -- Thorsten Altenkirch, Neil Ghani, Peter Hancock, Conor McBride, Peter Morris
  -- http://www.cs.nott.ac.uk/~psztxa/publ/jcont.pdf
  
  -- [3] "W-types: good news and bad news"
  -- Conor McBride
  -- http://mazzo.li/epilogue/index.html%3Fp=324.html
