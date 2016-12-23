{-# OPTIONS --type-in-type #-}

-- If this renders incorrectly, it's also available at 
-- This post is a sequel of the previous post [1]. There we've seen how simple algebraic effects
-- can be modeled in a dependently typed language. This time we'll see how Idris-like
-- resource-dependent effects [2] can be defined such that the non-termination and
-- "Codensity" effects are expressible too. The reader is assumed to be familiar with Idris effects.

module HEff where

-- Some prelude first.

open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Sum
open import Data.Product as Product
open import Data.List.Base hiding ([_])

module Prelude where
  infix 3 _∈_ _∈₁_ _∈²_
  infix 4 [_]_≅_

  instance
    inj₁-instance : ∀ {A B} {{x : A}} -> A ⊎ B
    inj₁-instance {{x}} = inj₁ x

    inj₂-instance : ∀ {A B} {{y : B}} -> A ⊎ B
    inj₂-instance {{y}} = inj₂ y

  -- See https://lists.chalmers.se/pipermail/agda/2016/009069.html
  [_]_≅_ : ∀ {A x₁ x₂} -> (B : A -> Set) -> B x₁ -> B x₂ -> Set
  [ B ] y₁ ≅ y₂ = _≡_ {A = ∃ B} (, y₁) (, y₂)

  _<×>_ : ∀ {A} -> (A -> Set) -> (A -> Set) -> A -> Set
  (B <×> C) x = B x × C x

  _∈_ : ∀ {A} -> A -> List A -> Set
  y ∈ []     = ⊥
  y ∈ x ∷ xs = y ≡ x ⊎ y ∈ xs

  -- `List₁` is defined as a function rather than a data, because this way we get
  -- eta-expansion for free. I'm not sure if this is needed in the code below,
  -- but it was needed when I was writing a library some time ago.
  List₁ : ∀ {A} -> (A -> Set) -> List A -> Set
  List₁ B  []      = ⊤
  List₁ B (x ∷ xs) = B x × List₁ B xs

  head₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> B x
  head₁ (y , ys) = y

  tail₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> List₁ B xs
  tail₁ (y , ys) = ys

  _∈₁_ : ∀ {A x xs} {B : A -> Set} -> B x -> List₁ B xs -> Set
  _∈₁_ {xs = []   }     z  tt      = ⊥
  _∈₁_ {xs = _ ∷ _} {B} z (y , ys) = [ B ] y ≅ z ⊎ z ∈₁ ys

  replace₁ : ∀ {A} {B : A -> Set} {x} {xs : List A} {y : B x} {ys : List₁ B xs}
           -> B x -> y ∈₁ ys -> List₁ B xs
  replace₁ {xs = []   } {ys = tt    } z  ()
  replace₁ {xs = _ ∷ _} {ys = y , ys} z (inj₁ refl) = z , ys
  replace₁ {xs = _ ∷ _} {ys = y , ys} z (inj₂ p)    = y , replace₁ z p

  -- `x , y ∈² xs , ys` is a proof that `x` occurs at the same index in `xs` as `y` in `ys`.
  _∈²_ : ∀ {A x xs} {B C : A -> Set} -> B x × C x -> List₁ B xs × List₁ C xs -> Set
  _∈²_ {xs = []   }         (y₁ , z₁) (tt        , tt       ) = ⊥
  _∈²_ {xs = _ ∷ _} {B} {C} (y₁ , z₁) ((y₂ , ys) , (z₂ , zs)) =
    [ B <×> C ] (y₁ , z₁) ≅ (y₂ , z₂) ⊎ y₁ , z₁ ∈² ys , zs

  to∈₁ : ∀ {A x xs} {B C : A -> Set} {y : B x} {z : C x} {ys : List₁ B xs} {zs : List₁ C xs}
       -> y , z ∈² ys , zs -> z ∈₁ zs
  to∈₁ {xs = []   }  ()
  to∈₁ {xs = _ ∷ _} (inj₁ refl) = inj₁ refl
  to∈₁ {xs = _ ∷ _} (inj₂ p)    = inj₂ (to∈₁ p)

  Sets : Set
  Sets = List Set

  HList : Sets -> Set
  HList = List₁ id
open Prelude

module EffectModule where
  -- The type of effects in Idris is defined like this:

  -- Effect : Type
  -- Effect = (result : Type) ->
  --          (input_resource : Type) ->
  --          (output_resource : result -> Type) -> Type

  -- We'll use a similar definition. There are two differences:
  -- 1) Since resources are not necessary types,
  -- `Effect` is parametrized by the type of its resources.
  -- 2) `input_resource` is the first argument, because it's often a parameter of some particular
  -- effect and Agda explicitly distinguishes between parameters and indices unlike Idris
  -- (and hence it's often convenient to define an effect without an `input_resource`,
  -- and bound `input_resource` in parameters telescope instead).

  -- So the definition could be

  -- Effect : Set -> Set
  -- Effect R = R -> (A : Set) -> (A -> R) -> Set

  -- where `R` is the type of resources of an effect, but we split the definition due to
  -- the parameters-indices distinction mentioned above:

  -- `Effectful` is `Effect` without `input_resource`.
  Effectful : ∀ {R} -> Set
  Effectful {R} = (A : Set) -> (A -> R) -> Set
 
  Effect : Set -> Set
  Effect R = R -> Effectful {R}

  ResourcesTypes : Set
  ResourcesTypes = Sets

  -- `Ψs : Effects Rs` is a list of effects typed over a list of resources types `Rs`.
  Effects : ResourcesTypes -> Set
  Effects = List₁ Effect

  -- `rs : Resources Rs` is a heterogeneous list of resources of types from `Rs`.
  Resources : ResourcesTypes -> Set
  Resources = HList

  -- A higher effect is an effect that is defined over a list of simple effects and
  -- transforms resources of those effects. This notion will be motivated later.
  HigherEffect : Set
  HigherEffect = ∀ {Rs} -> Effects Rs -> Effect (Resources Rs)

  HigherEffects : Set
  HigherEffects = List HigherEffect

  record HApply {Rs} (Φ : HigherEffect) (Ψs : Effects Rs) rs A rs′ : Set where
    constructor happlied
    field getHApplied : Φ Ψs rs A rs′

  -- At first I defined this as a data type, but Agda doesn't keep track of polarity of indices
  -- and thus doesn't see that `Codensity` below is strictly positive when `Unionʰᵉ` is a data.
  -- The `HApply` wrapper allows to infer `Φ` from `Unionʰᵉ (Φ ∷ Φs) Ψs Rs A rs′` just like
  -- with the data version.
  Unionʰᵉ : HigherEffects -> HigherEffect
  Unionʰᵉ  []      Ψs rs A rs′ = ⊥
  Unionʰᵉ (Φ ∷ Φs) Ψs rs A rs′ = HApply Φ Ψs rs A rs′ ⊎ Unionʰᵉ Φs Ψs rs A rs′

  -- "Constructors" of `Unionʰᵉ`.
  pattern hereʰᵉ  a = inj₁ (happlied a)
  pattern thereʰᵉ a = inj₂  a

  -- The union of simple effects is a higher effect.
  -- This is a direct counterpart of `Unionᵉ` defined in the previous post.
  data Unionᵉ : HigherEffect where
    -- Injecting an effect into some union of effects
    -- changes the resource at the position where the effect occurs (1).
    hereᵉ  : ∀ {R Rs r A r′ rs} {Ψ : Effect R} {Ψs : Effects Rs}
           -> Ψ r A r′ -> Unionᵉ (Ψ , Ψs) (r , rs) A (λ x -> r′ x , rs)
    -- Injecting an effect into some union of effects
    -- doesn't change the resources of all other effects.
    thereᵉ : ∀ {R Rs r A rs rs′} {Ψ : Effect R} {Ψs : Effects Rs}
           -> Unionᵉ Ψs rs A rs′ -> Unionᵉ (Ψ , Ψs) (r , rs) A (λ x -> r , rs′ x)

  hinj : ∀ {Φ Φs Rs rs A rs′} {Ψs : Effects Rs}
       -> Φ ∈ Φs -> Φ Ψs rs A rs′ -> Unionʰᵉ Φs Ψs rs A rs′
  hinj {Φs = []}     ()
  hinj {Φs = _ ∷ _} (inj₁ refl) = hereʰᵉ
  hinj {Φs = _ ∷ _} (inj₂ p)    = thereʰᵉ ∘ hinj p

  -- This is another way to express (1).
  inj′ : ∀ {R Rs r A r′ rs} {Ψ : Effect R} {Ψs : Effects Rs}
       -> (p : Ψ , r ∈² Ψs , rs) -> Ψ r A r′ -> Unionᵉ Ψs rs A (λ x -> replace₁ (r′ x) (to∈₁ p))
  inj′ {Rs = []}     ()
  inj′ {Rs = _ ∷ _} (inj₁ refl) = hereᵉ
  inj′ {Rs = _ ∷ _} (inj₂ p)    = thereᵉ ∘ inj′ p

  -- If an effect doesn't change its resource, then the resources of the union of effects
  -- don't change as well.
  inj : ∀ {R Rs r A rs} {Ψ : Effect R} {Ψs : Effects Rs}
      -> Ψ , r ∈² Ψs , rs -> Ψ r A (const r) -> Unionᵉ Ψs rs A (const rs)
  inj {Rs = []}     ()
  inj {Rs = _ ∷ _} (inj₁ refl) = hereᵉ
  inj {Rs = _ ∷ _} (inj₂ p)    = thereᵉ ∘ inj p
open EffectModule

module IFreerModule where
  infixl 2 _>>=_ _>=>_
  infixr 1 _>>_
  infixl 6 _<$>_ _<*>_

  -- `IFreer` is the indexed counterpart of `Freer` and it's an effect transformer too.
  -- `IFreer` is a Hoare state monad (in the sense of [3]; [4] is relevant here too).
  data IFreer {R} (Ψ : Effect R) : Effect R where
    return : ∀ {B r′} y -> IFreer Ψ (r′ y) B r′
    call   : ∀ {r A r′ B r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′

  liftᶠ : ∀ {R r A r′} {Ψ : Effect R} -> Ψ r A r′ -> IFreer Ψ r A r′
  liftᶠ a = call a return

  _>>=_ : ∀ {R r B r′ C r′′} {Ψ : Effect R}
        -> IFreer Ψ r B r′ -> (∀ y -> IFreer Ψ (r′ y) C r′′) -> IFreer Ψ r C r′′
  return y >>= g = g y
  call a f >>= g = call a λ x -> f x >>= g

  _>=>_ : ∀ {R A B r₂ C r₃} {Ψ : Effect R} {r₁ : A -> R}
        -> (∀ x -> IFreer Ψ (r₁ x) B r₂)
        -> (∀ y -> IFreer Ψ (r₂ y) C r₃)
        -> (∀ x -> IFreer Ψ (r₁ x) C r₃)
  (f >=> g) x = f x >>= g

  _>>_ : ∀ {R r₁ B r₂ C r′′} {Ψ : Effect R}
       -> IFreer Ψ r₁ B (const r₂) -> IFreer Ψ r₂ C r′′ -> IFreer Ψ r₁ C r′′
  b >> c = b >>= const c

  _<$>_ : ∀ {R r₁ B r₂ C} {Ψ : Effect R}
        -> (B -> C) -> IFreer Ψ r₁ B (const r₂) -> IFreer Ψ r₁ C (const r₂)
  g <$> b = b >>= return ∘ g

  _<*>_ : ∀ {R r₁ B r₂ C r₃} {Ψ : Effect R}
        -> IFreer Ψ r₁ (B -> C) (const r₂)
        -> IFreer Ψ r₂  B       (const r₃)
        -> IFreer Ψ r₁  C       (const r₃)
  h <*> b = h >>= _<$> b

  hoistIFreer : ∀ {R r B r′} {Ψ Φ : Effect R}
              -> (∀ {r A r′} -> Ψ r A r′ -> Φ r A r′) -> IFreer Ψ r B r′ -> IFreer Φ r B r′
  hoistIFreer h (return y) = return y
  hoistIFreer h (call a f) = call (h a) λ x -> hoistIFreer h (f x)
open IFreerModule

module EffModule where
  -- Some convenience.
  pattern simple a k = call (hereʰᵉ  a) k
  pattern higher a k = call (thereʰᵉ a) k

  -- The main definition. `HEff` describes a computation over a list of simple effects
  -- and a list of higher effects that contains the `Unionᵉ` higher effect.
  -- The idea is that besides performing some local effectful calls like getting
  -- the state in a stateful computation, we can also perform some "big" effectful calls that
  -- can change resources of several simple effects. This is why `Unionᵉ` is a higher effect --
  -- it's aware of resources of simple effects and changes the row of resources
  -- (by transforming one particular resource) when a simple effectful call is performed.
  -- Unlike `Eff` in Idris `HEff` doesn't allow to change effects -- only their resources.
  HEff : HigherEffects -> HigherEffect
  HEff Φs Ψs = IFreer (Unionʰᵉ (Unionᵉ ∷ Φs) Ψs)

  hinvoke : ∀ {Φ Φs Rs rs A rs′} {Ψs : Effects Rs} {{p : Φ ∈ Φs}}
          -> Φ Ψs rs A rs′ -> HEff Φs Ψs rs A rs′
  hinvoke {{p}} = liftᶠ ∘ thereʰᵉ ∘ hinj p

  invoke′ : ∀ {Φs R Rs r A r′ rs} {Ψ : Effect R} {Ψs : Effects Rs} {{p : Ψ , r ∈² Ψs , rs}}
          -> Ψ r A r′ -> HEff Φs Ψs rs A (λ x -> replace₁ (r′ x) (to∈₁ p))
  invoke′ {{p}} = liftᶠ ∘ hereʰᵉ ∘ inj′ p

  invoke : ∀ {Φs R Rs r A rs} {Ψ : Effect R} {Ψs : Effects Rs} {{p : Ψ , r ∈² Ψs , rs}}
         -> Ψ r A (const r) -> HEff Φs Ψs rs A (const rs)
  invoke {{p}} = liftᶠ ∘ hereʰᵉ ∘ inj p

  -- An equivalent of `execEff` from the previous post, only for higher effects.
  hexecEff : ∀ {Φs Rs rs B rs′ rs′′} {Φ : HigherEffect} {Ψs : Effects Rs}
           -> (∀ y -> HEff Φs Ψs (rs′ y) B rs′′)
           -> (∀ {rs A rs′}
               -> Φ Ψs rs A rs′
               -> (∀ x -> HEff Φs Ψs (rs′ x) B rs′′)
               -> HEff Φs Ψs rs B rs′′)
           -> HEff (Φ ∷ Φs) Ψs rs B rs′
           -> HEff  Φs      Ψs rs B rs′′
  hexecEff eta phi (return y)             = eta y
  hexecEff eta phi (simple  a          k) = simple a λ x -> hexecEff eta phi (k x)
  hexecEff eta phi (higher (hereʰᵉ  a) k) = phi    a λ x -> hexecEff eta phi (k x)
  hexecEff eta phi (higher (thereʰᵉ a) k) = higher a λ x -> hexecEff eta phi (k x)

  hshift : ∀ {Φs Rs rs B rs′} {Φ : HigherEffect} {Ψs : Effects Rs}
         -> HEff Φs Ψs rs B rs′ -> HEff (Φ ∷ Φs) Ψs rs B rs′
  hshift = hoistIFreer λ
    { (hereʰᵉ  a) -> hereʰᵉ   a
    ; (thereʰᵉ a) -> thereʰᵉ (thereʰᵉ a)
    }

  -- `Eff` describes a computation with no higher effects except for `Unionᵉ`.
  -- I.e. it's the usual `Eff`.
  Eff : HigherEffect
  Eff = HEff []

  runEff : ∀ {A} -> Eff tt tt A (const tt) -> A
  runEff (return x)    = x
  runEff (simple () _)
  runEff (higher () _)
open EffModule

module StateModule where
  -- The heterogeneous state effect. Its resource is of type `Set`.
  -- `Get` doesn't changes the resource. `Put` changes the resource
  -- from `S` (the current state) to `T` (the state after `Put` is called).
  data State S : Effectful where
    Get : State S S (const S)
    Put : ∀ {T} -> T -> State S ⊤ (const T)

  get : ∀ {Φs Rs S rs} {Ψs : Effects Rs} {{p : State , S ∈² Ψs , rs}}
      -> HEff Φs Ψs rs S _
  get {{p}} = invoke {{p}} Get

  zap : ∀ {Φs Rs rs T} {Ψs : Effects Rs} S {{p : State , S ∈² Ψs , rs}}
      -> T -> HEff Φs Ψs rs ⊤ _
  zap S {{p}} = invoke′ {{p}} ∘ Put

  put : ∀ {Φs Rs S rs} {Ψs : Effects Rs} {{p : State , S ∈² Ψs , rs}}
      -> S -> HEff Φs Ψs rs ⊤ (const rs)
  put {{p}} = invoke {{p}} ∘ Put

  modify′ : ∀ {Φs Rs S rs T} {Ψs : Effects Rs} {{p : State , S ∈² Ψs , rs}}
          -> (S -> T) -> HEff Φs Ψs rs ⊤ _
  modify′ {{p}} f = get >>= zap _ {{p}} ∘ f

  modify : ∀ {Φs Rs S rs} {Ψs : Effects Rs} {{p : State , S ∈² Ψs , rs}}
         -> (S -> S) -> HEff Φs Ψs rs ⊤ _
  modify f = get >>= put ∘ f

  -- `rs′` returns a final resource of `State` and final resources of other effects, hence
  -- when the `State` effect is handled resulting computation returns a value of the same type
  -- as the original computations returns plus a final resource of `State`.
  -- I.e. this is like the usual `S -> B × S`, but, since the state is heterogeneous and
  -- can depend on the value returned, it's more like `S -> Σ B T`.
  -- Resources of all other effects remain untouched.
  execState : ∀ {Rs S rs B rs′} {Ψs : Effects Rs}
            -> S
            -> Eff (State , Ψs) (S , rs)  B                   rs′
            -> Eff  Ψs           rs      (Σ B (head₁ ∘ rs′)) (tail₁ ∘ rs′ ∘ proj₁)
  execState s (return y)            = return (y , s)
  execState s (simple (hereᵉ  a) k) with a
  ... | Get    = execState s  (k s)
  ... | Put s' = execState s' (k tt)
  execState s (simple (thereᵉ a) k) = simple a λ x -> execState s (k x)
  execState s (higher ()         k)
open StateModule

module ErrorModule where
  -- The error effect is almost the same as before, since its resource is trivial.
  data Error E : Effect ⊤ where
    Throw : E -> Error E _ ⊥ _

  -- Note that `throw` transforms initial resources into whatever other resources.
  -- Indeed, we need to be able to throws errors via the `Error` effect in any part of
  -- a computation: it's not required that initial and final resources must match --
  -- `throw` is not `return`.
  throw : ∀ {Φs Rs E rs B rs′} {Ψs : Effects Rs} {{p : Error E , tt ∈² Ψs , rs}}
        -> E -> HEff Φs Ψs rs B rs′
  throw {{p}} e = invoke {{p}} (Throw e) >>= ⊥-elim

  -- But this means that if a computation threw an error, it's not known in what state
  -- resources were. I.e. resources became existential. Therefore in order to handle `Error`,
  -- we must "deexistentialize" resources. Hence `execError` returns a computation that
  -- returns `E ⊎ B` like before, but also attaches `Resources Rs` to `E`. I.e. if a computation
  -- threw an error, then return also resources so we can make them final via `[ proj₂ , _ ]`
  execError : ∀ {Rs E rs B rs′} {Ψs : Effects Rs}
            -> Eff (Error E , Ψs) (tt , rs) B rs′
            -> Eff Ψs rs (E × Resources Rs ⊎ B) [ proj₂ , tail₁ ∘ rs′ ]′
  execError (return y)                   = return (inj₂  y)
  execError (simple (hereᵉ (Throw e)) k) = return (inj₁ (e , _))
  execError (simple (thereᵉ a       ) k) = simple a λ x -> execError (k x)
  execError (higher  ()               k)

  -- But having exisentials means there is some CPS lying around.
  -- Instead of returning resources on failing we can just handle errors such that
  -- no matter what resources are, they are always transformed to what is required.
  catchError : ∀ {Rs E rs B rs′} {Ψs : Effects Rs}
             -> Eff (Error E , Ψs) (tt , rs) B rs′
             -> (∀ {rs} -> E -> Eff Ψs rs B (tail₁ ∘ rs′))
             -> Eff Ψs rs B (tail₁ ∘ rs′)
  catchError (return y)                   h = return y
  catchError (simple (hereᵉ (Throw e)) k) h = h e
  catchError (simple (thereᵉ a       ) k) h = simple a λ x -> catchError (k x) h
  catchError (higher  ()               k) h
open ErrorModule

module StateTest where
  open import Data.Fin

  -- Here's an example.

  -- final resources producer ----------------------------|
  -- result is of type ----------------------------|      |
  -- initial resources ------------------|         |      |
  -- effects ----------|                 |         |      |
  fpred : Eff (Error ⊤ , State , tt) (tt , ℕ , tt) ℕ (λ n -> tt , Fin n , tt)
  fpred = get >>= λ
    {  0      -> throw tt
    ; (suc n) -> zap ℕ (fromℕ n) >> return (suc n)
    }

  -- `fpred` gets the current state, if it's `0`, then it throws an error,
  -- if it's `suc n`, then puts `fromℕ n` in the state and returns `suc n`.
  -- Note that the type signature of `fpred` guarantees that the value in a final state
  -- is always of type `Fin n` where `n` is what the computation returned.
  -- And indeed `fromℕ n` has type `Fin (suc n)`.
  -- If we try to return `n` instead of `suc n` we'll get the following very useful error:

  -- No instance of type
  -- ((Set , State , ℕ) ≡ (⊤ , Error ⊤ , tt) ⊎
  --  (Set , State , ℕ) ≡ (Set , State , ℕ) ⊎ ⊥)
  -- was found in scope.

  -- But if we explicitly fill the instance argument to `zap` the error becomes

  -- suc x != x of type ℕ

  -- A more general type signature for `fpred`:

  -- fpred : ∀ {Rs rs} {Ψs : Effects Rs}
  --           {{err : Error ⊤ , tt ∈² Ψs , rs}} {{st : State , ℕ ∈² Ψs , rs}}
  --       -> Eff Ψs rs ℕ (λ n -> replace₁ (Fin n) (to∈₁ st))

  -- (Having to deal with `replace₁` is slightly annoying. Since resources are independent
  -- on each other, we perhaps can do better).

  -- A couple of tests:

  -- state ----------------------------------------------------------------|
  -- resources ----------------------------------------------------|       |
  -- error -------------------------------------------------|      |       |
  test₀ : (runEff ∘ execState 0 $ execError fpred) ≡ (inj₁ (tt , ℕ , tt) , 0)
  test₀ = refl

  -- state ----------------------------------------------------|
  -- result -----------------------------------------------|   |
  test₂ : (runEff ∘ execState 2 $ execError fpred) ≡ (inj₂ 2 , Fin.suc zero)
  test₂ = refl

module GeneralModule where
  -- Now general recursion stuff. Imagine a function that receives a value and returns some other
  -- value, but also performs various effectful calls and changes resources of effects.
  -- A delayed recursive call must change resources as well, because that's what an actual
  -- recursive call does. And hence we have a higher effect that transforms resources
  -- of simple effects.

  -- `General` is a true inductive family. See `rs′′` appears twice? The first one is what
  -- you pass to the effect and the second one is what a whole computation returns.
  -- I.e. a computation that has the `General A rs′ B rs′′` effect always returns `rs′′` as
  -- a final resources producer. If it pretends to return something else, then this something else
  -- unifies with `rs′′` once pattern matching on `Rec` is performed. This is just like with
  -- `x ≡ y`: you can write distinct `x` and `y` there, but once you pattern matched on `refl`,
  -- they're unified. Two appearances of `rs′` are treated similarly.
  data General {Rs} A (rs′ : A -> Resources Rs) (B : A -> Set)
               (rs′′ : ∀ {x} -> B x -> Resources Rs) : HigherEffect where
    Rec : ∀ {Ψs} x -> General A rs′ B rs′′ Ψs (rs′ x) (B x) rs′′

  -- The `λ {_} → ...` part is due to the notorious hidden-lambda bug (see [7]).
  rec : ∀ {Φs Rs A} {Ψs : Effects Rs} {rs′ : A -> Resources Rs}
          {B : A -> Set} {rs′′ : ∀ {x} -> B x -> Resources Rs}
          {{p : (λ {_} → General A rs′ B rs′′) ∈ Φs}}
      -> ∀ x -> HEff Φs Ψs (rs′ x) (B x) rs′′
  rec = hinvoke ∘ Rec

  -- A function of type `Π A Φs Ψs (λ x -> rs′ x , B x , rs′′)` is a function
  -- that receives a value of type `A`, can perform higher effects from `Φs` and
  -- simple effects from Ψs. Its initial resources of effects are `rs′ x` for the `x` received,
  -- it returns `B x` (for the same `x`) and the final resources producer is `rs′′`.
  Π : ∀ {Rs}
    -> (A : Set)
    -> HigherEffects
    -> Effects Rs
    -> (A -> Resources Rs × Σ Set λ B -> B -> Resources Rs)
    -> Set
  Π A Φs Ψs F = ∀ x -> let rs , B , rs′ = F x in
    HEff (General A (proj₁ ∘ F) (proj₁ ∘ proj₂ ∘ F) (proj₂ $ proj₂ (F _)) ∷ Φs) Ψs rs B rs′

  -- At the value level the next three functions are just the same as their non-dependent
  -- counterparts from the previous post.
  execGeneral : ∀ {Φs Rs A x} {Ψs : Effects Rs} {rs′ : A -> Resources Rs}
                  {B : A -> Set} {rs′′ : ∀ {x} -> B x -> Resources Rs}
              -> (∀ x -> HEff Φs Ψs (rs′ x) (B x) rs′′)
              -> HEff (General A rs′ B rs′′ ∷ Φs) Ψs (rs′ x) (B x) rs′′
              -> HEff  Φs                         Ψs (rs′ x) (B x) rs′′
  execGeneral {Φs} {Rs} {A} {x} {Ψs} {rs′} {B} {rs′′} f = hexecEff return h where
    -- This is where the aforementioned unification plays its role.
    -- Pattern matching on `Rec` reveals that universally quantified `rs` is actually `rs′ x`
    -- and the final resources producers are unified too.
    h : ∀ {rs Bx rs′′′}
      -> General A rs′ B rs′′ Ψs rs Bx rs′′′
      -> ((y : Bx) -> HEff Φs Ψs (rs′′′ y) (B x) rs′′)
      -> HEff Φs Ψs rs (B x) rs′′
    h (Rec x) k = f x >>= k

  {-# NON_TERMINATING #-}
  execApply : ∀ {Φs Rs A F} {Ψs : Effects Rs} -> Π A Φs Ψs F -> ∀ x -> HEff Φs Ψs _ _ _
  execApply f x = execGeneral (execApply f) (f x)

  execPetrol : ∀ {Φs Rs A} {Ψs : Effects Rs} {F} {{p : ∀ {x} -> Error ⊤ , tt ∈² Ψs , proj₁ (F x)}}
             -> ℕ -> Π A Φs Ψs F -> ∀ x -> HEff Φs Ψs _ _ _
  execPetrol  0      f x = throw tt
  execPetrol (suc n) f x = execGeneral (λ x -> execPetrol n f x) (f x)
open GeneralModule

module TestGeneral where
  open import Data.Fin hiding (_+_)
  open import Data.Vec as Vec hiding (_>>=_; sum)

  -- Here is a contrived example.
  -- The type level reads as follows: `ones` receives a number and returns an effectful
  -- computation that has the `State` and `General` effects; initially, a `Fin (suc n)` is
  -- in the state; the computation returns a list of numbers `xs` and puts
  -- a `Vec ℕ n × Fin (suc (sum xs))` into the state.
  -- At the value level `ones` performs delayed recursive calls until the `Fin` in the state is
  -- `zero`. An argument to delayed recursive calls grows at each call (from `n` to `suc n`).
  -- When a `Fin` becomes `zero`, we put a vector of `0`s and `zero` into the state.
  -- But since `n` was grown, the length of the vector is greater than original `n` and
  -- hence after each delayed recursive call we truncate the vector (and also grow a `Fin`):
  -- the `modify′ {{p}} (Product.map Vec.tail suc)` part. In order to be able to grow a `Fin`,
  -- we must prepend `1` to the resulting list, because `suc` transforms a `Fin n` into a
  -- `Fin (suc n)` and we can't violate the guarantees provided by type signature.
  -- So `ones` truncates the `Fin` in the state before each recursive call, performs the call
  -- and grows the `Fin` back, thus the `Fin` in a final state is always the same as in an initial.
  ones : ∀ {Rs} {Ψs : Effects Rs} {rs : Resources Rs}
       -> Π ℕ [] (State , Ψs) λ n -> (Fin (suc n) , rs)
                                   , List ℕ
                                   , λ xs -> (Vec ℕ n × Fin (suc (sum xs))) , rs
  ones n = get {{p}} >>= λ
    {  zero   -> zap _ {{p}} (Vec.replicate 0 , zero) >> return []
    ; (suc i) -> zap _ {{p}} (inject₁ (inject₁ i)) >>
                 rec {{p}} (suc n) >>= λ xs ->
                 modify′ {{p}} (Product.map Vec.tail suc) >>
                 return (1 ∷ xs)
    } where pattern p = inj₁ refl

  -- `p` is a number of steps to perform, `i` is an initial `Fin` in the state.
  run : ℕ -> Fin 4 -> ⊤ × ⊤ ⊎ ∃ λ xs -> Vec ℕ 3 × Fin (suc (sum xs))
  run p i = runEff ∘ execError ∘ execState i $ execPetrol p ones 3

  test₀ : ∀ {n} -> run (suc n) zero ≡ inj₂ ([] , 0 ∷ 0 ∷ 0 ∷ [] , zero)
  test₀ = refl

  test₁ : run 2 (suc zero) ≡ inj₂ (1 ∷ [] , 0 ∷ 0 ∷ 0 ∷ [] , suc zero)
  test₁ = refl

  test₂ : ∀ {n} -> run (3 + n) (suc (suc zero)) ≡ inj₂ (1 ∷ 1 ∷ [] , 0 ∷ 0 ∷ 0 ∷ [] , suc (suc zero))
  test₂ = refl

  test₃ : run 3 (suc (suc (suc zero))) ≡ inj₁ (tt , tt)
  test₃ = refl

module CodensityModule where
  infixl 2 _⟨>>=⟩_ _⟨>>=⟩′_
  infixr 1 _⟨>>⟩_

  -- Let's see another example of a higher effect.

  -- Free monads and their relatives are known to be inefficient wrt left-nested binds.
  -- The situation is similar to that of lists: left-nested appends result in quadratic performance,
  -- while right-nested appends have linear performance. A common way to mitigate the situation
  -- is to use difference lists: they have O(1) append and it takes O(n) time to reify a difference
  -- list into an actual one. The same trick can be used to improve performance of free monads and
  -- that's what [5] does.
  -- [6] takes a different perspective: instead of performing binds the authors chose to collect
  -- them in a data type which gives same O(1) `bind`. Their approach is much smarter than what
  -- I'm going to show and I believe it should be adopted in a practical library (there would be
  -- termination checking issues, but they probably can be solved with sized types), but
  -- nevertheless this example is nice.

  -- Here is the effect. Looks quite intimidating, right? But the idea is simple: we package
  -- an effectful computation (which has this same `Codensity` effect too) with a bind continuation
  -- instead of actually performing `_>>=_`.
  data Codensity Φs : HigherEffect where
    Bind : ∀ {Rs rs B rs′ C rs′′} {Ψs : Effects Rs}
         -> HEff (Codensity Φs ∷ Φs) Ψs rs B rs′
         -> (∀ y -> HEff Φs Ψs (rs′ y) C rs′′)
         -> Codensity Φs Ψs rs C rs′′

  -- And this is what we get on invoking `Bind`. The idea is that left-nested calls to `_⟨>>=⟩_`
  -- stack via the `Codensity` effect instead of being computed like with `_>>=_`.
  -- Right-nested calls are disallowed so far, since the bind continuation doesn't have the
  -- `Codensity` effect.
  _⟨>>=⟩_ : ∀ {Φs Rs rs B rs′ C rs′′} {Ψs : Effects Rs} 
          -> HEff (Codensity Φs ∷ Φs) Ψs rs B rs′
          -> (∀ y -> HEff Φs Ψs (rs′ y) C rs′′)
          -> HEff (Codensity Φs ∷ Φs) Ψs rs C rs′′
  b ⟨>>=⟩ g = hinvoke (Bind b g)

  _⟨>>⟩_ : ∀ {Φs Rs rs₁ B rs₂ C rs′′} {Ψs : Effects Rs} 
         -> HEff (Codensity Φs ∷ Φs) Ψs rs₁ B (const rs₂)
         -> HEff  Φs                 Ψs rs₂ C  rs′′
         -> HEff (Codensity Φs ∷ Φs) Ψs rs₁ C  rs′′
  b ⟨>>⟩ c = b ⟨>>=⟩ const c

  -- Here we reassociate binds via CPS by growing the `k₃` continuation.
  -- Just like with difference lists.
  bindCodensity : ∀ {Φs Rs rs B rs′ C rs′′} {Ψs : Effects Rs}
                -> HEff (Codensity Φs ∷ Φs) Ψs rs B rs′
                -> (∀ y -> HEff Φs Ψs (rs′ y) C rs′′)
                -> HEff Φs Ψs rs C rs′′
  bindCodensity (return y)                       k₃ = k₃ y
  bindCodensity (simple  a                   k₂) k₃ = simple a λ x -> bindCodensity (k₂ x) k₃
  bindCodensity (higher (hereʰᵉ (Bind a k₁)) k₂) k₃ =
    bindCodensity a (k₁ >=> λ x -> bindCodensity (k₂ x) k₃)
  bindCodensity (higher (thereʰᵉ a)          k₂) k₃ = higher a λ x -> bindCodensity (k₂ x) k₃

  execCodensity : ∀ {Φs Rs rs B rs′} {Ψs : Effects Rs}
                -> HEff (Codensity Φs ∷ Φs) Ψs rs B rs′ -> HEff Φs Ψs rs B rs′
  execCodensity b = bindCodensity b return

  -- We can also have right-nested computations with the `Codensity` effect.
  -- I don't know if we lose much by handling `Codenisty` so early or not, though.
  _⟨>>=⟩′_ : ∀ {Φs Rs rs B rs′ C rs′′} {Ψs : Effects Rs} 
           -> HEff (Codensity Φs ∷ Φs) Ψs rs B rs′
           -> (∀ y -> HEff (Codensity Φs ∷ Φs) Ψs (rs′ y) C rs′′)
           -> HEff (Codensity Φs ∷ Φs) Ψs rs C rs′′
  b ⟨>>=⟩′ g = b ⟨>>=⟩ execCodensity ∘ g
open CodensityModule

module TestCodensity where
  -- This is `replicateM` that generates left-nested `_>>_`s.
  replicateLeftM : ∀ {Φs Rs rs B} {Ψs : Effects Rs} 
                 -> ℕ -> HEff Φs Ψs rs B (const rs) -> HEff Φs Ψs rs ⊤ (const rs)
  replicateLeftM {Φs} {Rs} {rs} {B} {Ψs} n e = go n eₜₜ where
    eₜₜ = _ <$> e

    go : ℕ -> HEff Φs Ψs rs ⊤ (const rs) -> HEff Φs Ψs rs ⊤ (const rs)
    go  0      a = return tt
    go  1      a = a
    go (suc n) a = go n (a >> eₜₜ)

  -- This is `replicateM` that generates left-nested `_⟨>>⟩_`s.
  replicateCoLeftM : ∀ {Φs Rs rs B} {Ψs : Effects Rs} 
                   -> ℕ
                   -> HEff  Φs                 Ψs rs B (const rs)
                   -> HEff (Codensity Φs ∷ Φs) Ψs rs ⊤ (const rs)
  replicateCoLeftM {Φs} {Rs} {rs} {B} {Ψs} n e = go n (hshift eₜₜ) where
    eₜₜ = _ <$> e

    go : ℕ
       -> HEff (Codensity Φs ∷ Φs) Ψs rs ⊤ (const rs)
       -> HEff (Codensity Φs ∷ Φs) Ψs rs ⊤ (const rs)
    go  0      a = return tt
    go  1      a = a
    go (suc n) a = go n (a ⟨>>⟩ eₜₜ)

  -- Uncomment this and memory consumption will grow from 117 MB to 880 MB.
  -- test₁ : (proj₂ ∘ runEff ∘ execState 0 ∘ replicateLeftM 80 $ modify suc) ≡ 80
  -- test₁ = refl

  -- Uncomment this and memory consumption will grow from 117 MB to 160 MB.
  -- This version type checks much faster as expected.
  -- test₂ : (proj₂ ∘ runEff ∘ execState 0 ∘ execCodensity ∘ replicateCoLeftM 80 $ modify suc) ≡ 80
  -- test₂ = refl

module Remarks where
  -- Resource-dependent effects seem rather nice,
  -- There are problem with resources

module References where
  -- [1] "Turing-completeness totally freer"
  -- http://effectfully.blogspot.com/2016/12/turing-completeness-totally-freer.html

  -- [2] "The Effects Tutorial"
  -- http://docs.idris-lang.org/en/latest/effects/

  -- [3] "Inferring Precise Polymorphic Specifications for the Hoare State Monad",
  -- Cole Schlesinger and Nikhil Swamy
  -- http://research.microsoft.com/en-us/um/people/nswamy/paper.pdf

  -- [4] "The Hoare State Monad", Wouter Swierstra
  -- http://www.staff.science.uu.nl/~swier004/talks/2009-eindhoven.pdf

  -- [5] "Asymptotic Improvement of Computations over Free Monads"
  -- http://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf

  -- [6] "Freer Monads, More Extensible Effects", Oleg Kiselyov, Hiromi Ishii
  -- http://okmij.org/ftp/Haskell/extensible/more.pdf

  -- [7] "Eliminating the problems of hidden-lambda insertion", Marcus Johansson, Jesper Lloyd
  -- http://www2.tcs.ifi.lmu.de/~abel/MScThesisJohanssonLloyd.pdf
