module SC.Prelude where

open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Base
open import Data.Nat                      hiding (_≟_)
open import Data.Fin
open import Data.Fin.Properties as FinP   hiding (_≟_)
open import Data.String         as String hiding (_≟_; _==_)
open import Data.Maybe          as Maybe
open import Data.Product        as Prod
open import Data.List           as List
open import Category.Monad
open RawMonad {{...}} public

infix 7 _==_

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {x y v w s t}
      -> (f : A -> B -> C -> D) -> x ≡ y -> v ≡ w -> s ≡ t -> f x v s ≡ f y w t
cong₃ f refl refl refl = refl

record ProperRawMonoid {α} (M : Set α) : Set (Level.suc α) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    _≈_ : M -> M -> Set α
    _∙_ : M -> M -> M
    ε   : M
open ProperRawMonoid {{...}}

instance
  List-monoid : ∀ {α} {A : Set α} -> ProperRawMonoid (List A)
  List-monoid = record { _≈_ = _≡_ ; _∙_ = List._++_ ; ε = [] }

  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = Maybe.monad

  ×-Monad : ∀ {α ℓ} {A : Set α} {{_ : ProperRawMonoid A}} -> RawMonad {α Level.⊔ ℓ} (A ×_)
  ×-Monad = record { return = λ x -> ε , x ; _>>=_ = λ { (x , y) f -> Prod.map (x ∙_) id (f y) } }

record DecEq {α} (A : Set α) : Set α where
  infix 4 _≟_
  field _≟_ : Decidable (_≡_ {A = A})
open DecEq {{...}} public

instance
  DecEq-Fin    : ∀ {n} -> DecEq (Fin n) 
  DecEq-Fin    = record { _≟_ =   FinP._≟_ }

  DecEq-String : DecEq String
  DecEq-String = record { _≟_ = String._≟_ }

_==_ : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> A -> Bool
n == m = ⌊ n ≟ m ⌋

elem : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> Bool
elem x  []      = false
elem x (y ∷ xs) = x == y ∨ elem x xs

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : DecEq A}}
           -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if x == y then just z else lookup-for x xs

deletem : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> Maybe (List A)
deletem x  []      = nothing
deletem x (y ∷ xs) = if x == y then just xs else (y ∷_) <$> deletem x xs

delete : ∀ {α} {A : Set α} {{_ : DecEq A}} -> A -> List A -> List A
delete x xs = maybe id xs (deletem x xs)

nub : ∀ {α} {A : Set α} {{_ : DecEq A}} -> List A -> List A
nub = List.foldr (λ x r -> x ∷ delete x r) []
