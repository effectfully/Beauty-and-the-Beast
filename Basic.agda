module SC.Basic where

open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat.Base hiding (erase)
open import Data.Nat.Show
open import Data.Fin
open import Data.Maybe.Base
open import Data.Product
open import Data.List.Base
open import Coinduction
open import Data.String.Base as String renaming (String to Name) hiding (_++_; show) public

open import SC.Prelude public

_++ℕ_ : Name -> ℕ -> Name
n ++ℕ i = n String.++ show i

infixr 5 _⇒_
infixl 6 _▻_
infix  3 _∈_ _⊆_
infixr 4 vs_
infixr 3 ƛ_ fix_
infixl 6 _·_
infixr 5 _::_
infix  5 _≟'_

-- Do we really need this? We can just compare ordinary terms.
data Spine : Set where
  var  : Spine
  ƛ_   : Spine -> Spine
  _·_  : Spine -> Spine -> Spine
  fix_ : Spine -> Spine
  z        : Spine
  s        : Spine -> Spine
  caseNat  : Spine -> Spine -> Spine -> Spine
  nil      : Spine
  _::_     : Spine -> Spine -> Spine
  caseList : Spine -> Spine -> Spine -> Spine

_≟'_ : (x y : Spine) -> Maybe (x ≡ y)
var     ≟' var     = just refl
(ƛ x)   ≟' (ƛ y)   = cong ƛ_ <$> x ≟' y
(f · x) ≟' (g · y) = cong₂ _·_ <$> f ≟' g ⊛ x ≟' y
(fix f) ≟' (fix g) = cong fix_ <$> f ≟' g
z               ≟' z               = just refl
s n             ≟' s m             = cong s <$> n ≟' m
caseNat  n  x f ≟' caseNat  m  y g = cong₃ caseNat  <$> n  ≟' m  ⊛ x ≟' y ⊛ f ≟' g
nil             ≟' nil             = just refl
(x :: xs)       ≟' (y :: ys)       = cong₂ _::_ <$> x ≟' y ⊛ xs ≟' ys
caseList xs x f ≟' caseList ys y g = cong₃ caseList <$> xs ≟' ys ⊛ x ≟' y ⊛ f ≟' g
_ ≟' _ = nothing

instance
  DecEq-Spine : DecEq Spine
  DecEq-Spine = record { _≟_ = λ x y -> maybe′ yes (no (const ⊥)) (x ≟' y) }
    where postulate ⊥ : _

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

lengthᶜᵒⁿ : Con -> ℕ
lengthᶜᵒⁿ  ε      = 0
lengthᶜᵒⁿ (Γ ▻ σ) = suc (lengthᶜᵒⁿ Γ)

∈-to-Fin : ∀ {Γ σ} -> σ ∈ Γ -> Fin (lengthᶜᵒⁿ Γ)
∈-to-Fin  vz    = zero
∈-to-Fin (vs v) = suc (∈-to-Fin v)

weakenᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
weakenᵛᵃʳ  stop     v     = v
weakenᵛᵃʳ (skip ψ)  v     = vs (weakenᵛᵃʳ ψ v)
weakenᵛᵃʳ (keep ψ)  vz    = vz
weakenᵛᵃʳ (keep ψ) (vs v) = vs (weakenᵛᵃʳ ψ v)

unweakenᵛᵃʳ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Δ -> Maybe (σ ∈ Γ)
unweakenᵛᵃʳ  stop     v     = just v
unweakenᵛᵃʳ (skip ψ)  vz    = nothing
unweakenᵛᵃʳ (skip ψ) (vs v) = unweakenᵛᵃʳ ψ v
unweakenᵛᵃʳ (keep ψ)  vz    = just vz
unweakenᵛᵃʳ (keep ψ) (vs v) = vs_ <$> unweakenᵛᵃʳ ψ v

top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
top = skip stop

_∘ˢᵘᵇ_ : ∀ {Γ Δ Θ} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢᵘᵇ ψ      = ψ
skip φ ∘ˢᵘᵇ ψ      = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ stop   = keep φ
keep φ ∘ˢᵘᵇ skip ψ = skip (φ ∘ˢᵘᵇ ψ)
keep φ ∘ˢᵘᵇ keep ψ = keep (φ ∘ˢᵘᵇ ψ)

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

  spine : ∀ {Γ σ} -> Γ ⊢ σ -> Spine
  spine (var v) = var
  spine (ƛ b)   = ƛ (spine b)
  spine (f · x) = spine f · spine x
  spine (fix f) = fix (spine f)
  spine  z                = z
  spine (s n)             = s (spine n)
  spine (caseNat  n  y g) = caseNat  (spine n)  (spine y) (spine g)
  spine  nil              = nil
  spine (x :: xs)         = spine x :: spine xs
  spine (caseList xs y g) = caseList (spine xs) (spine y) (spine g)

  Term : Type -> Set
  Term σ = ∀ {Γ} -> Γ ⊢ σ

  fv : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Δ ⊢ σ -> List (Fin (lengthᶜᵒⁿ Γ))
  fv ψ (var v) = fromMaybe (∈-to-Fin <$> unweakenᵛᵃʳ ψ v)
  fv ψ (ƛ b)   = fv (skip ψ) b
  fv ψ (f · x) = fv ψ f ++ fv ψ x
  fv ψ (fix f) = fv ψ f
  fv ψ  z                = []
  fv ψ (s n)             = fv ψ n
  fv ψ (caseNat  n  y g) = fv ψ n  ++ fv ψ y ++ fv ψ g
  fv ψ  nil              = []
  fv ψ (x :: xs)         = fv ψ x ++ fv ψ xs
  fv ψ (caseList xs y g) = fv ψ xs ++ fv ψ y ++ fv ψ g

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

weakenʷ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ʷ σ
weakenʷ ψ = weaken ψ ∘ toʷ

infix 3 _⊢∞_

data _⊢∞_ (Γ : Con) : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ      -> Γ ⊢∞ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢∞ τ -> Γ ⊢∞ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢∞ σ ⇒ τ -> Γ ⊢∞ σ     -> Γ ⊢∞ τ
  z        :            Γ ⊢∞ nat
  s        :            Γ ⊢∞ nat    -> Γ ⊢∞ nat
  caseNat  : ∀ {σ}   -> Γ ⊢∞ nat    -> Γ ⊢∞ σ      -> Γ ⊢∞ nat ⇒ σ        -> Γ ⊢∞ σ
  nil      : ∀ {σ}   -> Γ ⊢∞ list σ
  _::_     : ∀ {σ}   -> Γ ⊢∞ σ      -> Γ ⊢∞ list σ -> Γ ⊢∞ list σ
  caseList : ∀ {σ τ} -> Γ ⊢∞ list σ -> Γ ⊢∞ τ      -> Γ ⊢∞ σ ⇒ list σ ⇒ τ -> Γ ⊢∞ τ
  checkpoint : ∀ {σ} -> Bool -> Name -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ
  
data Result : Set where
  var : Name   -> Result
  lam : Name   -> Result -> Result
  _·_ : Result -> Result -> Result
  Let_:=_In_ : Name -> Result -> Result -> Result
  z        : Result
  s        : Result -> Result
  caseNat  : Result -> Result -> Result -> Result
  nil      : Result
  _::_     : Result -> Result -> Result
  caseList : Result -> Result -> Result -> Result
