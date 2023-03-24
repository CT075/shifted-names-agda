module Data.Var.Base where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.Bool using (if_then_else_)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Effect.Functor
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Shifted names are a variation on locally-nameless types, in which each name
-- is annotated with an index marking how many times it's been shadowed.
--
-- It's worth noting that [Bound] in this formulation uses de Bruijin _levels_
-- (0 refers to the outermost binding), not de Bruijin _indicies_ (0 refers to
-- the innermost binding). This was the numbering scheme used by Dolan and
-- repeated here, as it simplifies the operation definitions a lot.

record Name : Set where
  constructor N
  field
    name : String
    index : ℕ

bump : String → Name → Name
bump x (N y i) = if x == y then N y (suc i) else N y i

lower : ∀{T : Set} → (Name → T) → T → String → Name → T
lower free bzero x (N y zero) = if x == y then bzero else free (N y zero)
lower free bzero x (N y (suc i)) = if x == y then free (N y i) else free (N y (suc i))

variable
  n : ℕ

data Var n : Set where
  Bound : Fin n → Var n
  Free : Name → Var n

openVar : String → Var (suc n) → Var n
openVar x (Bound zero) = Free (N x zero)
openVar x (Bound (suc i)) = Bound i
openVar x (Free name) = Free (bump x name)

closeVar : String → Var n → Var (suc n)
closeVar x (Bound i) = Bound (suc i)
closeVar x (Free name) = lower Free (Bound zero) x name

wkVar : Var n → Var (suc n)
wkVar (Bound i) = Bound (suc i)
wkVar (Free name) = Free name

shiftVar : String → Var n → Var n
shiftVar x v = openVar x (wkVar v)

renameVar : String → String → Var n → Var n
renameVar y x v = openVar y (closeVar x v)

-- CR-someday cam: this probably shouldn't live here
record FunctorExt {ℓ ℓ'}
    (F : Set ℓ → Set ℓ')
    {{R : RawFunctor F}} : Set (lsuc ℓ ⊔ ℓ') where
  open RawFunctor R public
  field
    fmap-∘ : ∀{A B C} {f : B → C} {g : A → B} {x : F A} →
      ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))

open FunctorExt {{...}}

-- Simple generalization of variable-level transforms to full ASTs

openT : ∀ {ℓ} {T : Set → Set ℓ} → {{R : RawFunctor T}} → {{FunctorExt T}} →
  String → T (Var (suc n)) → T (Var n)
openT x = openVar x <$>_

closeT : ∀ {T : Set → Set} → {{R : RawFunctor T}} → {{FunctorExt T}} →
  String → T (Var n) → T (Var (suc n))
closeT x = closeVar x <$>_

wkT : ∀ {T : Set → Set} → {{R : RawFunctor T}} → {{FunctorExt T}} →
  T (Var n) → T (Var (suc n))
wkT = wkVar <$>_

shiftT : ∀ {T : Set → Set} → {{R : RawFunctor T}} → {{FunctorExt T}} →
  String → T (Var n) → T (Var n)
shiftT x = shiftVar x <$>_

renameT : ∀ {T : Set → Set} → {{R : RawFunctor T}} → {{FunctorExt T}} →
  String → String → T (Var n) → T (Var n)
renameT y x = renameVar y x <$>_

-- A [Subst T S] substitutes an [S] for a variable in [T]. In most cases, we
-- will have [S n = T (Var n)]. However, sometimes we want to restrict what
-- forms can be substituted where (such as only allowing variables to be
-- substituted for one another).
record Subst {ℓ}
    (T : Set → Set ℓ)
    (S : ℕ → Set)
    {{R : RawFunctor T}} {{Ext : FunctorExt T}} : Set ℓ where
  field
    var : Var n → S n
    join : T (S n) → T (Var n)

  bindVar : S n → Var (suc n) → S n
  bindVar u (Bound zero) = u
  bindVar u (Bound (suc n)) = var (Bound n)
  bindVar u (Free name) = var (Free name)

  bindT : S n → T (Var (suc n)) → T (Var n)
  bindT u t = join (bindVar u <$> t)
