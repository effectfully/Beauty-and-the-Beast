module SC.Basic where

open import SC.Prelude public

infixr 6 _⇒_
infixl 5 _▻_
infix  4 _⊆_ _∈_ _∋_ _⊢_
infix  3 ƛ_ fix_
infixl 6 _·_
infixr 5 _::_

mutual
  data Base : Set where
    bnat  : Base
    blist : Type -> Base

  data Type : Set where
    base : Base -> Type
    _⇒_  : Type -> Type -> Type

pattern nat    = base  bnat
pattern list σ = base (blist σ)

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data _⊆_ : Con -> Con -> Set where
  stop : ∀ {Γ}     -> Γ ⊆ Γ
  skip : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ σ
  keep : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ

data _∈_ σ : Con -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ

Links : Set₁
Links = Con -> Type -> Set

Renames : Links -> Set
Renames _∙_ = ∀ {σ Γ Δ} -> Γ ⊆ Δ -> Γ ∙ σ -> Δ ∙ σ

_∸>_ : Links -> Links -> Set
_∙_ ∸> _◆_ = ∀ {σ Γ} -> Γ ∙ σ -> Γ ◆ σ

_∋_ : Links
_∋_ = flip _∈_

lenᶜ : Con -> ℕ
lenᶜ  ε      = 0
lenᶜ (Γ ▻ σ) = suc (lenᶜ Γ)

top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
top = skip stop

_∘ˢ_ : ∀ {Γ Δ Ξ} -> Δ ⊆ Ξ -> Γ ⊆ Δ -> Γ ⊆ Ξ
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ stop   = keep κ
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

∈-to-Fin : ∀ {Γ σ} -> σ ∈ Γ -> Fin (lenᶜ Γ)
∈-to-Fin  vz    = zero
∈-to-Fin (vs v) = suc (∈-to-Fin v)

ren : Renames _∋_
ren  stop     v     = v
ren (skip ι)  v     = vs (ren ι v)
ren (keep ι)  vz    = vz
ren (keep ι) (vs v) = vs (ren ι v)

unren : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Δ -> Maybe (σ ∈ Γ)
unren  stop     v     = just v
unren (skip ι)  vz    = nothing
unren (skip ι) (vs v) = unren ι v
unren (keep ι)  vz    = just vz
unren (keep ι) (vs v) = vs_ <$> unren ι v

module ConstructorsMutual (ne nf : Links) where
  infix 4 _∙ⁿᵉ_ _∙ⁿᶠ_
  _∙ⁿᵉ_ = ne
  _∙ⁿᶠ_ = nf

  Var = ∀ {Γ σ}   -> σ ∈ Γ       -> Γ ∙ⁿᵉ σ
  App = ∀ {Γ σ τ} -> Γ ∙ⁿᵉ σ ⇒ τ -> Γ ∙ⁿᶠ σ -> Γ ∙ⁿᵉ τ
  Fix = ∀ {Γ σ}   -> Γ ∙ⁿᶠ σ ⇒ σ -> Γ ∙ⁿᵉ σ
  CaseNat  = ∀ {Γ σ}   -> Γ ∙ⁿᵉ nat    -> Γ ∙ⁿᶠ σ -> Γ ∙ⁿᶠ nat ⇒ σ        -> Γ ∙ⁿᵉ σ
  CaseList = ∀ {Γ σ τ} -> Γ ∙ⁿᵉ list σ -> Γ ∙ⁿᶠ τ -> Γ ∙ⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ∙ⁿᵉ τ

  Ne  = ∀ {Γ σ}   -> Γ ∙ⁿᵉ σ     -> Γ ∙ⁿᶠ σ
  Lam = ∀ {Γ σ τ} -> Γ ▻ σ ∙ⁿᶠ τ -> Γ ∙ⁿᶠ σ ⇒ τ
  Z    = ∀ {Γ}   -> Γ ∙ⁿᶠ nat
  S    = ∀ {Γ}   -> Γ ∙ⁿᶠ nat    -> Γ ∙ⁿᶠ nat
  Nil  = ∀ {Γ σ} -> Γ ∙ⁿᶠ list σ
  Cons = ∀ {Γ σ} -> Γ ∙ⁿᶠ σ      -> Γ ∙ⁿᶠ list σ -> Γ ∙ⁿᶠ list σ

module Constructors links = ConstructorsMutual links links

data _⊢_ : Links

open Constructors _⊢_

data _⊢_ where
  var  : Var
  ƛ_   : Lam
  _·_  : App
  fix_ : Fix
  z        : Z
  s        : S
  caseNat  : CaseNat
  nil      : Nil
  _::_     : Cons
  caseList : CaseList

Term : Type -> Set
Term σ = ∀ {Γ} -> Γ ⊢ σ

renᵗ : Renames _⊢_
renᵗ ι (var v) = var (ren ι v)
renᵗ ι (ƛ b)   = ƛ (renᵗ (keep ι) b)
renᵗ ι (f · x) = renᵗ ι f · renᵗ ι x
renᵗ ι (fix f) = fix (renᵗ ι f)
renᵗ ι  z                = z
renᵗ ι (s n)             = s (renᵗ ι n)
renᵗ ι (caseNat  n  y g) = caseNat  (renᵗ ι n)  (renᵗ ι y) (renᵗ ι g)
renᵗ ι  nil              = nil
renᵗ ι (x :: xs)         = renᵗ ι x :: renᵗ ι xs
renᵗ ι (caseList xs y g) = caseList (renᵗ ι xs) (renᵗ ι y) (renᵗ ι g)

fv-all : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Δ ⊢ σ -> List (Fin (lenᶜ Γ))
fv-all ι (var v) = fromMaybe (∈-to-Fin <$> unren ι v)
fv-all ι (ƛ b)   = fv-all (skip ι) b
fv-all ι (f · x) = fv-all ι f ++ fv-all ι x
fv-all ι (fix f) = fv-all ι f
fv-all ι  z                = []
fv-all ι (s n)             = fv-all ι n
fv-all ι (caseNat  n  y g) = fv-all ι n  ++ fv-all ι y ++ fv-all ι g
fv-all ι  nil              = []
fv-all ι (x :: xs)         = fv-all ι x ++ fv-all ι xs
fv-all ι (caseList xs y g) = fv-all ι xs ++ fv-all ι y ++ fv-all ι g

fv : ∀ {Γ σ} -> Γ ⊢ σ -> List (Fin (lenᶜ Γ))
fv = nub ∘ fv-all stop
