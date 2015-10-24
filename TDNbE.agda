module SC.TDNbE where

open import SC.Basic
open import SC.NF
open import SC.Semantics

infix  4 _⊨_
infixl 6 _·ᵐ_

mutual
  _⊨_ : Links
  Γ ⊨ nat    = Γ ⊢ⁿᶠ nat -- (ℕ⁺ (Γ ⊢ⁿᵉ nat)) should work as well.
  Γ ⊨ list σ = Listᵐ Γ σ
  Γ ⊨ σ ⇒ τ  = Γ ⊢ⁿᵉ σ ⇒ τ ⊎ (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊨ σ -> Δ ⊨ τ)
  -- Agda doesn't want to accept (Kripke Γ σ τ) -- termination checking fails.

  Listᵐ : Links
  Listᵐ Γ σ = List⁺ (Γ ⊨ σ) (Γ ⊢ⁿᵉ list σ)

neᵐ : _⊢ⁿᵉ_ ∸> _⊨_
neᵐ {nat}    n = neⁿᶠ  n
neᵐ {list σ} n = list⁺ n
neᵐ {σ ⇒ τ}  n = inj₁  n

varᵐ : _∋_ ∸> _⊨_
varᵐ = neᵐ ∘ varⁿᵉ
  
open Kripkable record
  { _∙_  = _⊨_
  ; varˢ = varᵐ
  }

mutual
  renᵐ : Renames _⊨_
  renᵐ {nat}    ι n  = renⁿᶠ ι n
  renᵐ {list σ} ι xs = renListᵐ ι xs
  renᵐ {σ ⇒ τ}  ι x  = smap (renⁿᵉ ι) (renᵏ ι) x

  renListᵐ : Renames Listᵐ
  renListᵐ ι (list⁺ xs) = list⁺ (renⁿᵉ ι xs)
  renListᵐ ι  []⁺       = []⁺
  renListᵐ ι (x ∷⁺ xs)  = renᵐ ι x ∷⁺ renListᵐ ι xs

mutual
  readback : _⊨_ ∸> _⊢ⁿᶠ_
  readback {nat}     n       = n
  readback {list σ}  xs      = readbackList xs
  readback {σ ⇒ τ}  (inj₁ n) = neⁿᶠ n
  readback {σ ⇒ τ}  (inj₂ k) = ƛⁿᶠ (readback (apᵏ k))

  readbackList : ∀ {σ Γ} -> Listᵐ Γ σ -> Γ ⊢ⁿᶠ list σ
  readbackList (list⁺ xs) = neⁿᶠ xs
  readbackList  []⁺       = nilⁿᶠ
  readbackList (x ∷⁺ xs)  = readback x ::ⁿᶠ readbackList xs

open Constructors _⊨_

zᵐ : Z
zᵐ = zⁿᶠ

sᵐ : S
sᵐ = sⁿᶠ ∘ readback

_·ᵐ_ : App
inj₁ f ·ᵐ x = neᵐ (f ·ⁿᵉ readback x)
inj₂ k ·ᵐ x = k ·ᵏ x

fixᵐ : Fix
fixᵐ = neᵐ ∘ fixⁿᵉ ∘ readback

caseNatᵐ : CaseNat
caseNatᵐ (neⁿᶠ n) y g = neᵐ (caseNatⁿᵉ n (readback y) (readback g))
caseNatᵐ  zⁿᶠ     y g = y
caseNatᵐ (sⁿᶠ n)  y g = g ·ᵐ n

caseListᵐ : CaseList
caseListᵐ (list⁺ xs) y g = neᵐ (caseListⁿᵉ xs (readback y) (readback g))
caseListᵐ  []⁺       y g = y
caseListᵐ (x ∷⁺ xs)  y g = g ·ᵐ x ·ᵐ xs

open Environment record
  { renˢ = renᵐ }

open Semantics record
  { _◆_  = _⊨_
  ; embˢ = id
  ; lamˢ = inj₂
  ; _·ˢ_ = _·ᵐ_
  ; fixˢ = fixᵐ
  ; zˢ        = zᵐ
  ; sˢ        = sᵐ
  ; caseNatˢ  = caseNatᵐ
  ; nilˢ      = []⁺
  ; _::ˢ_     = _∷⁺_
  ; caseListˢ = caseListᵐ
  }

nf : _⊢_ ∸> _⊢ⁿᶠ_
nf = readback ∘ eval
