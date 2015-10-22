{-# OPTIONS --no-positivity-check #-}

module SC.NbE where

open import SC.Basic
open import SC.NF
open import SC.Semantics

infixl 6 _·ˢⁿᶠ_

module _ where
  infix  4 _⊢ˢⁿᵉ_ _⊢ˢⁿᶠ_
  infixl 6 _·ˢⁿᵉ_
  infixr 5 _::ˢⁿᶠ_

  data _⊢ˢⁿᵉ_ : Links
  data _⊢ˢⁿᶠ_ : Links
  varˢⁿᶠ : _∋_ ∸> _⊢ˢⁿᶠ_

  open ConstructorsMutual _⊢ˢⁿᵉ_ _⊢ˢⁿᶠ_
  open module Dummy = Kripkable record
    { _∙_  = _⊢ˢⁿᶠ_
    ; varˢ = varˢⁿᶠ
    }

  data _⊢ˢⁿᵉ_ where
    varˢⁿᵉ : Var
    _·ˢⁿᵉ_ : App
    fixˢⁿᵉ : Fix
    caseNatˢⁿᵉ  : CaseNat
    caseListˢⁿᵉ : CaseList

  data _⊢ˢⁿᶠ_ where
    neˢⁿᶠ  : Ne
    lamˢⁿᶠ : ∀ {Γ σ τ} -> Kripke Γ σ τ -> Γ ⊢ˢⁿᶠ σ ⇒ τ
    zˢⁿᶠ    : Z
    sˢⁿᶠ    : S
    nilˢⁿᶠ  : Nil
    _::ˢⁿᶠ_ : Cons

  varˢⁿᶠ = neˢⁿᶠ ∘ varˢⁿᵉ
open Dummy

mutual
  renˢⁿᵉ : Renames _⊢ˢⁿᵉ_
  renˢⁿᵉ ι (varˢⁿᵉ v) = varˢⁿᵉ (ren ι v)
  renˢⁿᵉ ι (f ·ˢⁿᵉ x) = renˢⁿᵉ ι f ·ˢⁿᵉ renˢⁿᶠ ι x
  renˢⁿᵉ ι (fixˢⁿᵉ f) = fixˢⁿᵉ (renˢⁿᶠ ι f)
  renˢⁿᵉ ι (caseNatˢⁿᵉ  n  y g) = caseNatˢⁿᵉ  (renˢⁿᵉ ι n)  (renˢⁿᶠ ι y) (renˢⁿᶠ ι g)
  renˢⁿᵉ ι (caseListˢⁿᵉ xs y g) = caseListˢⁿᵉ (renˢⁿᵉ ι xs) (renˢⁿᶠ ι y) (renˢⁿᶠ ι g)

  renˢⁿᶠ : Renames _⊢ˢⁿᶠ_
  renˢⁿᶠ ι (neˢⁿᶠ n)  = neˢⁿᶠ (renˢⁿᵉ ι n)
  renˢⁿᶠ ι (lamˢⁿᶠ k) = lamˢⁿᶠ (renᵏ ι k)
  renˢⁿᶠ ι  zˢⁿᶠ        = zˢⁿᶠ
  renˢⁿᶠ ι (sˢⁿᶠ n)     = sˢⁿᶠ (renˢⁿᶠ ι n)
  renˢⁿᶠ ι  nilˢⁿᶠ      = nilˢⁿᶠ
  renˢⁿᶠ ι (x ::ˢⁿᶠ xs) = renˢⁿᶠ ι x ::ˢⁿᶠ renˢⁿᶠ ι xs

open Constructors _⊢ˢⁿᶠ_

fixˢⁿᶠ : Fix
fixˢⁿᶠ = neˢⁿᶠ ∘ fixˢⁿᵉ

_·ˢⁿᶠ_ : App
neˢⁿᶠ  f ·ˢⁿᶠ x = neˢⁿᶠ (f ·ˢⁿᵉ x)
lamˢⁿᶠ k ·ˢⁿᶠ x = k ·ᵏ x

caseNatˢⁿᶠ  : CaseNat
caseNatˢⁿᶠ (neˢⁿᶠ n) y g = neˢⁿᶠ (caseNatˢⁿᵉ n y g)
caseNatˢⁿᶠ  zˢⁿᶠ     y g = y
caseNatˢⁿᶠ (sˢⁿᶠ n)  y g = g ·ˢⁿᶠ n

caseListˢⁿᶠ : CaseList
caseListˢⁿᶠ (neˢⁿᶠ xs)   y g = neˢⁿᶠ (caseListˢⁿᵉ xs y g)
caseListˢⁿᶠ  nilˢⁿᶠ      y g = y
caseListˢⁿᶠ (x ::ˢⁿᶠ xs) y g = g ·ˢⁿᶠ x ·ˢⁿᶠ xs

open Environment record
  { renˢ = renˢⁿᶠ }

open Semantics record
  { _◆_  = _⊢ˢⁿᶠ_
  ; embˢ = id
  ; lamˢ = lamˢⁿᶠ
  ; _·ˢ_ = _·ˢⁿᶠ_
  ; fixˢ = fixˢⁿᶠ
  ; zˢ        = zˢⁿᶠ
  ; sˢ        = sˢⁿᶠ
  ; caseNatˢ  = caseNatˢⁿᶠ
  ; nilˢ      = nilˢⁿᶠ
  ; _::ˢ_     = _::ˢⁿᶠ_
  ; caseListˢ = caseListˢⁿᶠ
  }

mutual
  quoteⁿᵉ : _⊢ˢⁿᵉ_ ∸> _⊢ⁿᵉ_
  quoteⁿᵉ (varˢⁿᵉ v) = varⁿᵉ v
  quoteⁿᵉ (f ·ˢⁿᵉ x) = quoteⁿᵉ f ·ⁿᵉ quoteⁿᶠ x
  quoteⁿᵉ (fixˢⁿᵉ f) = fixⁿᵉ (quoteⁿᶠ f)
  quoteⁿᵉ (caseNatˢⁿᵉ  n  y g) = caseNatⁿᵉ  (quoteⁿᵉ n)  (quoteⁿᶠ y) (quoteⁿᶠ g)
  quoteⁿᵉ (caseListˢⁿᵉ xs y g) = caseListⁿᵉ (quoteⁿᵉ xs) (quoteⁿᶠ y) (quoteⁿᶠ g)

  quoteⁿᶠ : _⊢ˢⁿᶠ_ ∸> _⊢ⁿᶠ_
  quoteⁿᶠ (neˢⁿᶠ x)  = neⁿᶠ (quoteⁿᵉ x)
  quoteⁿᶠ (lamˢⁿᶠ k) = ƛⁿᶠ (quoteⁿᶠ (k top (varˢⁿᶠ vz))) -- runᵏ k
  quoteⁿᶠ  zˢⁿᶠ        = zⁿᶠ
  quoteⁿᶠ (sˢⁿᶠ x)     = sⁿᶠ (quoteⁿᶠ x)
  quoteⁿᶠ  nilˢⁿᶠ      = nilⁿᶠ
  quoteⁿᶠ (x ::ˢⁿᶠ xs) = quoteⁿᶠ x ::ⁿᶠ quoteⁿᶠ xs

nf : _⊢_ ∸> _⊢ⁿᶠ_
nf = quoteⁿᶠ ∘ eval
