module SC.Basic where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (erase) renaming (_≟_ to _≟ℕ_)
open import Data.Maybe
open import Category.Monad
open import Coinduction
open module M {ℓ} = RawMonad {ℓ} monad public

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {x y v w s t}
      -> (f : A -> B -> C -> D) -> x ≡ y -> v ≡ w -> s ≡ t -> f x v s ≡ f y w t
cong₃ f refl refl refl = refl

infixr 5 _⇒_
infixl 6 _▻_
infix  3 _∈_ _⊆_
infixr 4 vs_
infixr 3 ƛ_ fix_
infixl 6 _·_
infixr 5 _::_
infix  5 _≟_

data Syntax : Set where
  -- var  : ℕ -> Syntax
  var  : Syntax
  ƛ_   : Syntax -> Syntax
  _·_  : Syntax -> Syntax -> Syntax
  fix_ : Syntax -> Syntax
  z        : Syntax
  s        : Syntax -> Syntax
  caseNat  : Syntax -> Syntax -> Syntax -> Syntax
  nil      : Syntax
  _::_     : Syntax -> Syntax -> Syntax
  caseList : Syntax -> Syntax -> Syntax -> Syntax

_≟_ : (x y : Syntax) -> Maybe (x ≡ y)
-- var v   ≟ var w   = cong var <$> decToMaybe (v ≟ℕ w)
var     ≟ var     = just refl
(ƛ x)   ≟ (ƛ y)   = cong ƛ_ <$> x ≟ y
(f · x) ≟ (g · y) = cong₂ _·_ <$> f ≟ g ⊛ x ≟ y
(fix f) ≟ (fix g) = cong fix_ <$> f ≟ g
z               ≟ z               = just refl
s n             ≟ s m             = cong s <$> n ≟ m
caseNat  n  x f ≟ caseNat  m  y g = cong₃ caseNat  <$> n  ≟ m  ⊛ x ≟ y ⊛ f ≟ g
nil             ≟ nil             = just refl
(x :: xs)       ≟ (y :: ys)       = cong₂ _::_ <$> x ≟ y ⊛ xs ≟ ys
caseList xs x f ≟ caseList ys y g = cong₃ caseList <$> xs ≟ ys ⊛ x ≟ y ⊛ f ≟ g
_ ≟ _ = nothing

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

data _⊆_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

fromᵛᵃʳ : ∀ {Γ σ} -> σ ∈ Γ -> ℕ
fromᵛᵃʳ  vz    = 0
fromᵛᵃʳ (vs v) = suc (fromᵛᵃʳ v)

top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
top = skip stop

_∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢᵘᵇ ψ      = ψ
skip φ ∘ˢᵘᵇ ψ      = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ stop   = keep φ
keep φ ∘ˢᵘᵇ skip ψ = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ keep ψ = keep (φ ∘ˢᵘᵇ ψ)

weakenᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
weakenᵛᵃʳ  stop     v     = v
weakenᵛᵃʳ (skip ψ)  v     = vs (weakenᵛᵃʳ ψ v)
weakenᵛᵃʳ (keep ψ)  vz    = vz
weakenᵛᵃʳ (keep ψ) (vs v) = vs (weakenᵛᵃʳ ψ v)

module Term where
  infix  3 _⊢_
  infixr 3 ƛ_ fix_
  infixl 6 _·_
  infixr 5 _::_

  data _⊢_ (Γ : Con) : Type -> Set where
    var  : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
    ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
    _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
    fix_ : ∀ {σ}   -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ
    z        :            Γ ⊢ nat
    s        :            Γ ⊢ nat    -> Γ ⊢ nat
    caseNat  : ∀ {σ}   -> Γ ⊢ nat    -> Γ ⊢ σ      -> Γ ⊢ nat ⇒ σ        -> Γ ⊢ σ
    nil      : ∀ {σ}   -> Γ ⊢ list σ
    _::_     : ∀ {σ}   -> Γ ⊢ σ      -> Γ ⊢ list σ -> Γ ⊢ list σ
    caseList : ∀ {σ τ} -> Γ ⊢ list σ -> Γ ⊢ τ      -> Γ ⊢ σ ⇒ list σ ⇒ τ -> Γ ⊢ τ

  erase : ∀ {Γ σ} -> Γ ⊢ σ -> Syntax
  -- erase (var v) = var (fromᵛᵃʳ v)
  erase (var v) = var
  erase (ƛ b)   = ƛ (erase b)
  erase (f · x) = erase f · erase x
  erase (fix f) = fix (erase f)
  erase  z                = z
  erase (s n)             = s (erase n)
  erase (caseNat  n  y g) = caseNat  (erase n)  (erase y) (erase g)
  erase  nil              = nil
  erase (x :: xs)         = erase x :: erase xs
  erase (caseList xs y g) = caseList (erase xs) (erase y) (erase g)

  Term : Type -> Set
  Term σ = ∀ {Γ} -> Γ ⊢ σ

module Termʷ where
  infix  3 _⊢_
  infixr 3 ƛ_ fix_
  infixl 6 _·_
  infixr 5 _::_

  data _⊢_ (Γ : Con) : Type -> Set where
    var    : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
    ƛ_     : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
    _·_    : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
    fix_   : ∀ {σ}   -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ
    weaken : ∀ {Ω σ} -> Ω ⊆ Γ     -> Ω ⊢ σ     -> Γ ⊢ σ

    z        :            Γ ⊢ nat
    s        :            Γ ⊢ nat    -> Γ ⊢ nat
    caseNat  : ∀ {σ}   -> Γ ⊢ nat    -> Γ ⊢ σ      -> Γ ⊢ nat ⇒ σ        -> Γ ⊢ σ
    nil      : ∀ {σ}   -> Γ ⊢ list σ
    _::_     : ∀ {σ}   -> Γ ⊢ σ      -> Γ ⊢ list σ -> Γ ⊢ list σ
    caseList : ∀ {σ τ} -> Γ ⊢ list σ -> Γ ⊢ τ      -> Γ ⊢ σ ⇒ list σ ⇒ τ -> Γ ⊢ τ

  Term : Type -> Set
  Term σ = ∀ {Γ} -> Γ ⊢ σ

open Term  public
open Termʷ public renaming (_⊢_ to _⊢ʷ_; module _⊢_ to _⊢ʷ_; Term to Termʷ)

toʷ : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ʷ σ
toʷ (var v) = var v
toʷ (ƛ b)   = ƛ (toʷ b)
toʷ (f · x) = toʷ f · toʷ x
toʷ (fix f) = fix toʷ f
toʷ  z                = z
toʷ (s n)             = s (toʷ n)
toʷ (caseNat  n  y g) = caseNat  (toʷ n)  (toʷ y) (toʷ g)
toʷ  nil              = nil
toʷ (x :: xs)         = toʷ x :: toʷ xs
toʷ (caseList xs y g) = caseList (toʷ xs) (toʷ y) (toʷ g)

fromʷ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ʷ σ -> Δ ⊢ σ
fromʷ φ (var v)      = var (weakenᵛᵃʳ φ v)
fromʷ φ (ƛ b)        = ƛ (fromʷ (keep φ) b)
fromʷ φ (f · x)      = fromʷ φ f · fromʷ φ x
fromʷ φ (fix f)      = fix fromʷ φ f
fromʷ φ (weaken ψ x) = fromʷ (φ ∘ˢᵘᵇ ψ) x
fromʷ φ  z                = z
fromʷ φ (s n)             = s (fromʷ φ n)
fromʷ φ (caseNat  n  y g) = caseNat  (fromʷ φ n)  (fromʷ φ y) (fromʷ φ g)
fromʷ φ  nil              = nil
fromʷ φ (x :: xs)         = fromʷ φ x :: fromʷ φ xs
fromʷ φ (caseList xs y g) = caseList (fromʷ φ xs) (fromʷ φ y) (fromʷ φ g)

unʷ : ∀ {Γ σ} -> Γ ⊢ʷ σ -> Γ ⊢ σ
unʷ = fromʷ stop

infix 3 _⊢∞_

data _⊢∞_ (Γ : Con) : Type -> Set where
  ƛ_ : ∀ {σ τ} -> Γ ▻ σ ⊢∞ τ -> Γ ⊢∞ σ ⇒ τ
  s        :            Γ ⊢∞ nat    -> Γ ⊢∞ nat
  caseNat  : ∀ {σ}   -> Γ ⊢  nat    -> Γ ⊢∞ σ      -> Γ ⊢∞ nat ⇒ σ        -> Γ ⊢∞ σ
  _::_     : ∀ {σ}   -> Γ ⊢∞ σ      -> Γ ⊢∞ list σ -> Γ ⊢∞ list σ
  caseList : ∀ {σ τ} -> Γ ⊢  list σ -> Γ ⊢∞ τ      -> Γ ⊢∞ σ ⇒ list σ ⇒ τ -> Γ ⊢∞ τ
  stop : ∀ {σ} -> Γ ⊢ σ ->    Γ ⊢∞ σ
  keep : ∀ {σ} -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ
