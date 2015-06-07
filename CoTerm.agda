{-# OPTIONS --copatterns #-}

module SC.CoTerm where

-- Is this representation better in any sense?

open import Data.String

infixr 5 _⇒_
infixl 6 _▻_
infix  3 _∈_ _⊢_ _⊢ᶜᵒ_
infixr 3 vs_
infixr 2 ƛ_
infixl 5 _·_
infixr 4 _::_

data Type : Set where
  _⇒_ : Type -> Type -> Type
  nat  : Type
  list : Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

mutual
  data _⊢_ (Γ : Con) : Type -> Set where
    var  : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
    ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
    _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
    rec  : ∀ {σ}   -> Γ ⊢ᶜᵒ σ   -> Γ ⊢ σ
    z        :            Γ ⊢ nat
    s        :            Γ ⊢ nat    -> Γ ⊢ nat
    caseNat  : ∀ {σ}   -> Γ ⊢ nat    -> Γ ⊢ σ      -> Γ ⊢ nat ⇒ σ        -> Γ ⊢ σ
    nil      : ∀ {σ}   -> Γ ⊢ list σ
    _::_     : ∀ {σ}   -> Γ ⊢ σ      -> Γ ⊢ list σ -> Γ ⊢ list σ
    caseList : ∀ {σ τ} -> Γ ⊢ list σ -> Γ ⊢ τ      -> Γ ⊢ σ ⇒ list σ ⇒ τ -> Γ ⊢ τ

  record _⊢ᶜᵒ_ Γ σ : Set where
    coinductive
    field
      name : String
      term : Γ ⊢ σ
open _⊢ᶜᵒ_

Term : Type -> Set
Term σ = ∀ {Γ} -> Γ ⊢ σ

CoTerm : Type -> Set
CoTerm σ = ∀ {Γ} -> Γ ⊢ᶜᵒ σ

map : ∀ {σ τ} -> CoTerm ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
name map = "map"
term map = ƛ ƛ caseList (var vz)
                  nil
                 (ƛ ƛ var (vs vs vs vz) · var (vs vz) :: rec map · var (vs vs vs vz) · var vz)

map-map : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
map-map = ƛ ƛ ƛ rec map · var (vs vs vz) · (rec map · var (vs vz) · var vz)
