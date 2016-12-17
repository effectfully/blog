{-# OPTIONS --type-in-type #-}

-- The title (except for the last letter) is shamelessly stolen from [1].
-- Here we consider how simple (as opposed to resource-dependent like in Idris) algebraic effects
-- can be handled in a dependently typed language and
-- how non-termination can be modeled as such an effect.

module Freer where

-- Some boring stuff.

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Sum
open import Data.Product
open import Data.List.Base

module Prelude where
  infix  4 _∈_

  instance
    inj₁-instance : ∀ {A B} {{x : A}} -> A ⊎ B
    inj₁-instance {{x}} = inj₁ x

    inj₂-instance : ∀ {A B} {{y : B}} -> A ⊎ B
    inj₂-instance {{y}} = inj₂ y

  -- `_∈_` is defined as a function rather than a data type, because to my experience
  -- instance search plays better with functions. 
  _∈_ : ∀ {A} -> A -> List A -> Set
  y ∈ []     = ⊥
  y ∈ x ∷ xs = y ≡ x ⊎ y ∈ xs
open Prelude

module EffectModule where
  -- Simple effects are just functors:
  
  Effect : Set
  Effect = Set -> Set

  Effects : Set
  Effects = List Effect

  -- We define the union of effects using explicit recursion instead of `foldr`,
  -- because this way Agda sees that `Unionᵉ` is constructor-headed and thus can infer
  -- `Ψs` if `Unionᵉ Ψs` is provided.
  Unionᵉ : Effects -> Effect
  Unionᵉ  []      A = ⊥
  Unionᵉ (Ψ ∷ Ψs) A = Ψ A ⊎ Unionᵉ Ψs A

  inj : ∀ {Ψ Ψs A} -> Ψ ∈ Ψs -> Ψ A -> Unionᵉ Ψs A
  inj {Ψs = []}     ()
  inj {Ψs = _ ∷ _} (inj₁ refl) = inj₁
  inj {Ψs = _ ∷ _} (inj₂ p)    = inj₂ ∘ inj p
open EffectModule

module FreerModule where
  infixl 2 _>>=_
  infixr 1 _>>_
  infixl 6 _<$>_ _<*>_

  -- McBride uses free monads over containers in his paper,
  -- but we'll be using Freer monads from [2], because I find them simpler, nicer and they
  -- can be extended to dependent effects in a very natural way.

  -- `call` receives a `Ψ A`, which can be seen as a command (or a request),
  -- and a continuation which expects a response in `A` and returns an effectful computation.
  -- We'll see examples later.
  data Freer (Ψ : Effect) : Effect where
    return : ∀ {B} -> B -> Freer Ψ B
    call   : ∀ {A B} -> Ψ A -> (A -> Freer Ψ B) -> Freer Ψ B

  -- Note that `∀ {A} -> Ψ A -> (A -> Freer Ψ B)` is isomorphic to `Ψ (Freer Ψ B)`,
  -- which is what can be found in the classical definition of `Free`.
  -- However `Ψ (Freer Ψ B)` is not strictly positive, so it can't be used in type theory.
  -- `Free F` is also a monad only if `F` is a functor, while `Freer Ψ` is always a monad.

  -- Free monads toolkit:

  liftᶠ : ∀ {Ψ A} -> Ψ A -> Freer Ψ A
  liftᶠ a = call a return

  _>>=_ : ∀ {Ψ B C} -> Freer Ψ B -> (B -> Freer Ψ C) -> Freer Ψ C
  return y >>= g = g y
  call a f >>= g = call a λ x -> f x >>= g

  _>>_ : ∀ {Ψ B C} -> Freer Ψ B -> Freer Ψ C -> Freer Ψ C
  b >> c = b >>= const c

  _<$>_ : ∀ {Ψ B C} -> (B -> C) -> Freer Ψ B -> Freer Ψ C
  g <$> b = b >>= return ∘ g

  _<*>_ : ∀ {Ψ B C} -> Freer Ψ (B -> C) -> Freer Ψ B -> Freer Ψ C
  h <*> b = h >>= _<$> b
open FreerModule

module EffModule where
  -- An effectful computation is just a Freer monad over the union of a list of effects.
  Eff : Effects -> Effect
  Eff = Freer ∘ Unionᵉ

  -- If there are no effects in an effectful computation, we can simply return its result.
  runEff : ∀ {B} -> Eff [] B -> B
  runEff (return  y) = y
  runEff (call () p)

  -- This function invokes a single effect.
  invoke : ∀ {Ψ Ψs A} {{p : Ψ ∈ Ψs}} -> Ψ A -> Eff Ψs A
  invoke {{p}} = liftᶠ ∘ inj p

  -- This function allows to handle the outermost effect.
  execEff : ∀ {Ψ Ψs B C}
          -> (B -> Eff Ψs C)
          -> (∀ {A} -> Ψ A -> (A -> Eff Ψs C) -> Eff Ψs C)
          -> Eff (Ψ ∷ Ψs) B
          -> Eff  Ψs      C
  execEff eta phi (return        y) = eta y
  execEff eta phi (call (inj₁ a) k) = phi  a λ x -> execEff eta phi (k x)
  execEff eta phi (call (inj₂ a) k) = call a λ x -> execEff eta phi (k x)
open EffModule

module StateModule where
  -- Our first example is `State`.

  data State (S : Set) : Effect where
    -- If the request is `Get`, then a response is in `S`, i.e. the current state.
    Get : State S S
    -- If the request is `Put s`, then a response is in `⊤`, i.e. the response is dummy.
    Put : S -> State S ⊤

  -- When handling effects, each response must be satisfied,
  -- so in order to handle `Get` a value of type `S` is required,
  -- and in order to handle `Put` a value of type `⊤` is required, i.e. `tt`.

  -- The `State` toolkit:

  get : ∀ {Ψs S} {{p : State S ∈ Ψs}} -> Eff Ψs S
  get = invoke Get

  put : ∀ {Ψs S} {{p : State S ∈ Ψs}} -> S -> Eff Ψs ⊤
  put = invoke ∘ Put

  modify : ∀ {Ψs S} {{p : State S ∈ Ψs}} -> (S -> S) -> Eff Ψs ⊤
  modify f = get >>= put ∘ f

  -- The `State` handler receives an initial state `s`.
  -- On `Get` the state is passed to the continuation and on `Put s'` the state is
  -- replaced by `s'` such that all future `Get`s will get `s'` rather than the old `s`
  -- (until a new `Put` is encountered). All other effects remain untouched.
  execState : ∀ {Ψs S B} -> S -> Eff (State S ∷ Ψs) B -> Eff Ψs (B × S)
  execState s (return y)               = return (y , s)
  execState s (call (inj₁  Get    ) k) = execState s  (k s)
  execState s (call (inj₁ (Put s')) k) = execState s' (k tt)
  execState s (call (inj₂  a      ) k) = call a λ x -> execState s (k x)
open StateModule

module ErrorModule where
  -- `Error` is the next effect. It could be defined as

  -- data Error E B : Set where
  --   Throw : E -> Error E B

  -- but I prefer this version as it plays better with universe polymorphism
  -- (which is disabled in this file):

  data Error E : Effect where
    Throw : E -> Error E ⊥

  throw : ∀ {Ψs E B} {{p : Error E ∈ Ψs}} -> E -> Eff Ψs B
  throw e = invoke (Throw e) >>= ⊥-elim

  runError : ∀ {E B} -> Error E B -> E
  runError (Throw e) = e

  -- `execError` handles `Error E` and returns a computation that
  -- returns either an error in `E` or a normal value.
  execError : ∀ {Ψs E B} -> Eff (Error E ∷ Ψs) B -> Eff Ψs (E ⊎ B)
  execError = execEff (return ∘ inj₂) (const ∘ return ∘ inj₁ ∘ runError)
open ErrorModule

module GeneralModule where
  -- Here comes non-termination.
  
  data General {A} (B : A -> Set) : Effect where
    Rec : ∀ x -> General B (B x)

  -- `rec` is a delayed recursive call. It allows to write `f (suc n) = rec n`
  -- instead of `f (suc n) = f n`. This matters when a function is not obviously terminating,
  -- so you can write its body by replacing recursive calls with `rec` everywhere (or somewhere)
  -- and then handle non-termination using a monad of your choice as [1] describes.

  rec : ∀ {Ψs A} {B : A -> Set} {{p : General B ∈ Ψs}} -> ∀ x -> Eff Ψs (B x)
  rec = invoke ∘ Rec

  -- An effectful counterpart of McBride's `Π`.
  -- A function of type `f : Π A Ψs B` is a function that receives an `x : A`,
  -- can perform effects from `Ψs`, can call `rec x` where `x : A` and
  -- receive responses in `B x`, and finally returns a `B x`.
  Π : ∀ A -> Effects -> (A -> Set) -> Set _
  Π A Ψs B = ∀ x -> Eff (General B ∷ Ψs) (B x)

  -- `execGeneral f a` replaces each `rec x` in a computation `a` with `f x`.
  -- I.e. each delayed recursive call becomes an actual call (but not recursive yet).
  execGeneral : ∀ {Ψs A C} {B : A -> Set}
              -> (∀ x -> Eff Ψs (B x)) -> Eff (General B ∷ Ψs) C -> Eff Ψs C
  execGeneral {Ψs} {A} {C} {B} f = execEff return h where
    h : ∀ {Bx} -> General B Bx -> (Bx -> Eff Ψs C) -> Eff Ψs C
    h (Rec x) k = f x >>= k

  -- This is how we can run a generally recursive computation.
  -- `execApply f x` just applies `f` to `x` and replaces each successive `rec x` with
  -- a call to `execApply f`. Thus the computation stops only when there are no more
  -- delayed recursive calls. Since `General` allows to model non-terminating computations,
  -- an attempt to run such computation can be NON_TERMINATING, obviously.
  {-# NON_TERMINATING #-}
  execApply : ∀ {Ψs A} {B : A -> Set} -> Π A Ψs B -> ∀ x -> Eff Ψs (B x)
  execApply f x = execGeneral (execApply f) (f x)

  -- But we can also define something safe. This is the McBride's petrol-driven semantics.
  -- If there is no petrol, throw a dummy error.
  -- If there is more petrol, force each delayed recursive call.
  -- Note that there are no fancy monad morphisms, we only require a list of effects to contain
  -- the `Error` effect.
  execPetrol : ∀ {Ψs A} {B : A -> Set} {{p : Error ⊤ ∈ Ψs}}
             -> ℕ -> Π A Ψs B -> ∀ x -> Eff Ψs (B x)
  execPetrol  0      f x = throw tt
  execPetrol (suc n) f x = execGeneral (execPetrol n f) (f x)

  -- I won't consider more involved semantics of non-termination from [1] here.
open GeneralModule

module Test where
  -- A function that halves a natural number.
  halve : ℕ -> ℕ
  halve (suc (suc n)) = suc (halve n)
  halve  _            = 0

  tryHalve : ℕ -> Maybe ℕ
  tryHalve n@(suc (suc _)) = just (halve n)
  tryHalve _               = nothing

  -- A generally recursive computation that halves a natural number repeatedly,
  -- collects all halves in a list and also stores the number of elements in the list in a state.
  -- Emphatically, this computation can't be defined using structural recursion directly
  -- (though, you can use fancy tricks (like in [3]) to achieve that).
  halves : ∀ {Ψs} {{p : State ℕ ∈ Ψs}} -> Π ℕ Ψs λ _ -> List ℕ
  halves n = modify suc >> (n ∷_) <$> maybe′ rec (return []) (tryHalve n)

  -- `run` receives a number of recursive calls to perform and a natural number to repeatedly halve.
  run : ℕ -> ℕ -> ⊤ ⊎ List ℕ × ℕ
  run p = runEff ∘ execError ∘ execState 0 ∘ execPetrol p halves

  -- Four step are enough to perform to repeatedly halve `10`.
  test₄ : run 4 10 ≡ inj₂ (10 ∷ 5 ∷ 2 ∷ 1 ∷ [] , 4)
  test₄ = refl

  -- But three are not.
  test₃ : run 3 10 ≡ inj₁ tt
  test₃ = refl

  -- Just another test.
  test₅ : run 5 12 ≡ inj₂ (12 ∷ 6 ∷ 3 ∷ 1 ∷ [] , 4)
  test₅ = refl

module Conclusion where
  -- We've seen how simple algebraic effects can be handled in a dependently typed setting
  -- and how non-termination can be modeled as such an effect.
  -- But we can also model Idris-like resource-dependent effects in a similar way
  -- and define a non-termination effect in this setting too.
  -- It's much more fun, so this is what I'll probably write about next time.

module References where
  -- [1] "Turing-Completeness Totally Free", Conor McBride
  -- https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf

  -- [2] "Freer Monads, More Extensible Effects", Oleg Kiselyov, Hiromi Ishii
  -- http://okmij.org/ftp/Haskell/extensible/more.pdf

  -- [3] "Assisting Agda's termination checker"
  -- http://stackoverflow.com/questions/19642921/assisting-agdas-termination-checker
