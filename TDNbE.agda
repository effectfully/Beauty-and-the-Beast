module SC.TDNbE where

open import SC.Basic
open import SC.Semantics

infix  4 _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊨_
infixl 6 _·ⁿᵉ_ _·ᵐ_
infixr 5 _::ⁿᶠ_

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ
    fixⁿᵉ : ∀ {σ}   -> Γ ⊢ⁿᶠ σ ⇒ σ -> Γ ⊢ⁿᵉ σ
    caseNatⁿᵉ  : ∀ {σ}   -> Γ ⊢ⁿᵉ nat    -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᶠ nat ⇒ σ        -> Γ ⊢ⁿᵉ σ
    caseListⁿᵉ : ∀ {σ τ} -> Γ ⊢ⁿᵉ list σ -> Γ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ  : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ
    zⁿᶠ    :          Γ ⊢ⁿᶠ nat
    sⁿᶠ    :          Γ ⊢ⁿᶠ nat    -> Γ ⊢ⁿᶠ nat
    nilⁿᶠ  : ∀ {σ} -> Γ ⊢ⁿᶠ list σ
    _::ⁿᶠ_ : ∀ {σ} -> Γ ⊢ⁿᶠ σ      -> Γ ⊢ⁿᶠ list σ -> Γ ⊢ⁿᶠ list σ

mutual
  embⁿᵉ : _⊢ⁿᵉ_ ∸> _⊢_
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x
  embⁿᵉ (fixⁿᵉ f) = fix (embⁿᶠ f)
  embⁿᵉ (caseNatⁿᵉ  n  y g) = caseNat  (embⁿᵉ n)  (embⁿᶠ y) (embⁿᶠ g)
  embⁿᵉ (caseListⁿᵉ xs y g) = caseList (embⁿᵉ xs) (embⁿᶠ y) (embⁿᶠ g)

  embⁿᶠ : _⊢ⁿᶠ_ ∸> _⊢_
  embⁿᶠ (neⁿᶠ x) = embⁿᵉ x
  embⁿᶠ (ƛⁿᶠ b)  = ƛ (embⁿᶠ b)
  embⁿᶠ  zⁿᶠ        = z
  embⁿᶠ (sⁿᶠ n)     = s (embⁿᶠ n)
  embⁿᶠ  nilⁿᶠ      = nil
  embⁿᶠ (x ::ⁿᶠ xs) = embⁿᶠ x :: embⁿᶠ xs

mutual
  renⁿᵉ : Renames _⊢ⁿᵉ_
  renⁿᵉ ι (varⁿᵉ v) = varⁿᵉ (ren ι v)
  renⁿᵉ ι (f ·ⁿᵉ x) = renⁿᵉ ι f ·ⁿᵉ renⁿᶠ ι x
  renⁿᵉ ι (fixⁿᵉ f) = fixⁿᵉ (renⁿᶠ ι f)
  renⁿᵉ ι (caseNatⁿᵉ  n  y g) = caseNatⁿᵉ  (renⁿᵉ ι n ) (renⁿᶠ ι y) (renⁿᶠ ι g)
  renⁿᵉ ι (caseListⁿᵉ xs y g) = caseListⁿᵉ (renⁿᵉ ι xs) (renⁿᶠ ι y) (renⁿᶠ ι g)

  renⁿᶠ : Renames _⊢ⁿᶠ_
  renⁿᶠ ι (neⁿᶠ n) = neⁿᶠ (renⁿᵉ ι n)
  renⁿᶠ ι (ƛⁿᶠ  b) = ƛⁿᶠ (renⁿᶠ (keep ι) b)
  renⁿᶠ ι  zⁿᶠ        = zⁿᶠ
  renⁿᶠ ι (sⁿᶠ n)     = sⁿᶠ (renⁿᶠ ι n)
  renⁿᶠ ι  nilⁿᶠ      = nilⁿᶠ
  renⁿᶠ ι (x ::ⁿᶠ xs) = renⁿᶠ ι x ::ⁿᶠ renⁿᶠ ι xs

mutual
  _⊨_ : Links
  -- (ℕ⁺ (Γ ⊢ⁿᵉ nat)) should work as well.
  Γ ⊨ nat    = Γ ⊢ⁿᶠ nat
  Γ ⊨ list σ = Listᵐ Γ σ
  -- Is there something like _->⁺_?
  Γ ⊨ σ ⇒ τ  = (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊨ σ -> Δ ⊨ τ) ⊎ Γ ⊢ⁿᵉ σ ⇒ τ

  Listᵐ : Links
  Listᵐ Γ σ = List⁺ (Γ ⊨ σ) (Γ ⊢ⁿᵉ list σ)

mutual
  renᵐ : Renames _⊨_
  renᵐ {nat}    ι n  = renⁿᶠ ι n
  renᵐ {list σ} ι xs = rensᵐ ι xs
  renᵐ {σ ⇒ τ}  ι x  = smap (λ k {_} κ -> k (κ ∘ˢ ι)) (renⁿᵉ ι) x

  rensᵐ : Renames Listᵐ
  rensᵐ ι (list⁺ xs) = list⁺ (renⁿᵉ ι xs)
  rensᵐ ι  []⁺       = []⁺
  rensᵐ ι (x ∷⁺ xs)  = renᵐ ι x ∷⁺ rensᵐ ι xs

neᵐ : _⊢ⁿᵉ_ ∸> _⊨_
neᵐ {nat}    n = neⁿᶠ  n
neᵐ {list σ} n = list⁺ n
neᵐ {σ ⇒ τ}  n = inj₂  n

varᵐ : _∋_ ∸> _⊨_
varᵐ = neᵐ ∘ varⁿᵉ

mutual
  readback : _⊨_ ∸> _⊢ⁿᶠ_
  readback {nat}     n       = n
  readback {list σ}  xs      = readbackList xs
  readback {σ ⇒ τ}  (inj₁ k) = ƛⁿᶠ (readback (k top (varᵐ vz)))
  readback {σ ⇒ τ}  (inj₂ n) = neⁿᶠ n

  readbackList : ∀ {σ Γ} -> Listᵐ Γ σ -> Γ ⊢ⁿᶠ list σ
  readbackList (list⁺ xs) = neⁿᶠ xs
  readbackList  []⁺       = nilⁿᶠ
  readbackList (x ∷⁺ xs)  = readback x ::ⁿᶠ readbackList xs

zᵐ : ∀ {Γ} -> Γ ⊨ nat
zᵐ = zⁿᶠ

sᵐ : ∀ {Γ} -> Γ ⊨ nat -> Γ ⊨ nat
sᵐ = sⁿᶠ ∘ readback

_·ᵐ_ : ∀ {Γ σ τ} -> Γ ⊨ σ ⇒ τ -> Γ ⊨ σ -> Γ ⊨ τ
inj₁ k ·ᵐ x = k stop x
inj₂ f ·ᵐ x = neᵐ (f ·ⁿᵉ readback x)

fixᵐ : ∀ {Γ σ} -> Γ ⊨ σ ⇒ σ -> Γ ⊨ σ
fixᵐ = neᵐ ∘ fixⁿᵉ ∘ readback

caseNatᵐ : ∀ {Γ σ} -> Γ ⊨ nat -> Γ ⊨ σ -> Γ ⊨ nat ⇒ σ -> Γ ⊨ σ
caseNatᵐ (neⁿᶠ n) y g = neᵐ (caseNatⁿᵉ n (readback y) (readback g))
caseNatᵐ  zⁿᶠ     y g = y
caseNatᵐ (sⁿᶠ n)  y g = g ·ᵐ n

caseListᵐ : ∀ {Γ σ τ} -> Γ ⊨ list σ -> Γ ⊨ τ -> Γ ⊨ σ ⇒ list σ ⇒ τ -> Γ ⊨ τ
caseListᵐ (list⁺ xs) y g = neᵐ (caseListⁿᵉ xs (readback y) (readback g))
caseListᵐ  []⁺       y g = y
caseListᵐ (x ∷⁺ xs)  y g = g ·ᵐ x ·ᵐ xs

envKit : EnvKit
envKit = record
  { _∙_  = _⊨_
  ; varᵏ = varᵐ
  ; renᵏ = renᵐ
  }

semKit : SemKit envKit
semKit = record
  { _◆_  = _⊨_
  ; embˢ = id
  ; lamˢ = inj₁
  ; _·ˢ_ = _·ᵐ_
  ; fixˢ = fixᵐ
  ; zˢ        = zᵐ
  ; sˢ        = sᵐ
  ; caseNatˢ  = caseNatᵐ
  ; nilˢ      = []⁺
  ; _::ˢ_     = _∷⁺_
  ; caseListˢ = caseListᵐ
  }

open Semantics semKit

nf : _⊢_ ∸> _⊢ⁿᶠ_
nf = readback ∘ eval
