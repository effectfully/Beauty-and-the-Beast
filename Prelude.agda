module SC.Prelude where

open import Level          renaming (zero to lzero; suc to lsuc)                  public
open import Coinduction    hiding (fold; unfold)                                  public
open import Function       hiding (_∋_)                                           public
open import Relation.Binary.PropositionalEquality hiding ([_]; decSetoid; setoid) public
open import Data.Empty                                                            public
open import Data.Unit.Base hiding (_≤_; module _≤_)                               public
open import Data.Bool.Base hiding (_≟_)                                           public
open import Data.Nat.Base  hiding (_≟_; _⊔_)                                      public
open import Data.Nat.Show                                                         public
open import Data.Fin       using (Fin; zero; suc)                                 public
open import Data.Maybe     hiding (module Eq; Eq)                                 public
open import Data.Sum       renaming (map to smap)                                 public
open import Data.Product   renaming (map to pmap; zip to pzip)                    public
open import Data.List.Base renaming (map to lmap; zip to lzip) hiding ([_])       public
open import Data.Vec       using (Vec; []; _∷_; toList; lookup)                   public
open import Category.Monad
open ≡-Reasoning                                                                  public
open RawMonad {{...}}      hiding (zipWith)                                       public

open import Relation.Nullary.Decidable
open import Data.Fin.Properties using (_≟_)
open import Data.String as String hiding (_++_; _==_; _≟_)

infixr 5 _∷⁺_

record Eq {α} (A : Set α) : Set α where
  infix 4 _==_
  field _==_ : A -> A -> Bool
open Eq {{...}} public

record Monoid {α} (A : Set α) : Set (lsuc α) where
  infixl 6 _⊕_
  field
    _⊕_ : A -> A -> A
    ε   : A
open Monoid {{...}}

data List⁺ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  list⁺ : B -> List⁺ A B
  []⁺   : List⁺ A B
  _∷⁺_  : A -> List⁺ A B -> List⁺ A B

instance
  Eq-Fin : ∀ {n} -> Eq (Fin n) 
  Eq-Fin = record { _==_ = λ i j -> ⌊ i ≟ j ⌋ }

  Eq-String : Eq String
  Eq-String = record { _==_ = String._==_ }

  List-Monoid : ∀ {α} {A : Set α} -> Monoid (List A)
  List-Monoid = record { _⊕_ = _++_ ; ε = [] }

  Maybe-monad : ∀ {ℓ} -> RawMonad {ℓ} Maybe
  Maybe-monad = monad

  ×-Monad : ∀ {α ℓ} {A : Set α} {{monoid : Monoid A}} -> RawMonad {α ⊔ ℓ} (A ×_)
  ×-Monad = record
    { return = λ x -> ε , x
    ; _>>=_  = λ{ (x , y) f -> pmap (x ⊕_) id (f y) }
    }

lenᵛ : ∀ {n α} {A : Set α} -> Vec A n -> ℕ
lenᵛ {n} _ = n

elem : ∀ {α} {A : Set α} {{_ : Eq A}} -> A -> List A -> Bool
elem x  []      = false
elem x (y ∷ xs) = (x == y) ∨ elem x xs

lookup-for : ∀ {α β} {A : Set α} {B : Set β} {{_ : Eq A}} -> A -> List (A × B) -> Maybe B
lookup-for x  []            = nothing
lookup-for x ((y , z) ∷ xs) = if x == y then just z else lookup-for x xs

deletem : ∀ {α} {A : Set α} {{_ : Eq A}} -> A -> List A -> Maybe (List A)
deletem x  []      = nothing
deletem x (y ∷ xs) = if x == y then just xs else (y ∷_) <$> deletem x xs

delete : ∀ {α} {A : Set α} {{_ : Eq A}} -> A -> List A -> List A
delete x xs = maybe id xs (deletem x xs)

nub : ∀ {α} {A : Set α} {{_ : Eq A}} -> List A -> List A
nub = foldr (λ x r -> x ∷ delete x r) []
