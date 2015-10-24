module SC.Semantics where

open import SC.Basic

-- Forgive me this.
record Kripkable : Set₁ where
  infix  4 _∙_
  infixr 9 _∘ᵏ_

  field
    _∙_  : Links
    varˢ : _∋_ ∸> _∙_

  Kripke : Con -> Type -> Type -> Set
  Kripke Γ σ τ = ∀ {Δ} -> Γ ⊆ Δ -> Δ ∙ σ -> Δ ∙ τ

  apᵏ : ∀ {Γ σ τ} -> Kripke Γ σ τ -> Γ ▻ σ ∙ τ
  apᵏ k = k top (varˢ vz)

  _·ᵏ_ : ∀ {Γ σ τ} -> Kripke Γ σ τ -> Γ ∙ σ -> Γ ∙ τ
  k ·ᵏ t = k stop t

  renᵏ : ∀ {Γ Δ σ τ} -> Γ ⊆ Δ -> Kripke Γ σ τ -> Kripke Δ σ τ
  renᵏ ι k κ = k (κ ∘ˢ ι)

  _∘ᵏ_ : ∀ {Γ σ τ ν} -> Kripke Γ τ ν -> Kripke Γ σ τ -> Kripke Γ σ ν
  (k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

  record Environment : Set where
    infix 4 _⊢*_

    field
      renˢ : Renames _∙_

    data _⊢*_ Δ : Con -> Set where
      Ø   : Δ ⊢* ε
      _▷_ : ∀ {Γ σ} -> Δ ⊢* Γ -> Δ ∙ σ -> Δ ⊢* Γ ▻ σ

    lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Δ ⊢* Γ -> Δ ∙ σ
    lookupᵉ  vz    (ρ ▷ t) = t
    lookupᵉ (vs v) (ρ ▷ t) = lookupᵉ v ρ

    renᵉ : ∀ {Γ Δ Ξ} -> Δ ⊆ Ξ -> Δ ⊢* Γ -> Ξ ⊢* Γ
    renᵉ ι  Ø      = Ø
    renᵉ ι (ρ ▷ t) = renᵉ ι ρ ▷ renˢ ι t

    keepᵉ : ∀ {Δ Γ σ} -> Δ ⊢* Γ -> Δ ▻ σ ⊢* Γ ▻ σ
    keepᵉ ρ = renᵉ top ρ ▷ varˢ vz

    idᵉ : ∀ {Γ} -> Γ ⊢* Γ
    idᵉ {ε}     = Ø
    idᵉ {Γ ▻ σ} = keepᵉ idᵉ

    record Semantics : Set₁ where
      infix  4 _◆_
      infixl 6 _·ˢ_
      infixr 5 _::ˢ_

      field
        _◆_  : Links
        embˢ : _∙_ ∸> _◆_
        lamˢ : ∀ {Γ σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ∙ σ -> Δ ◆ τ) -> Γ ◆ σ ⇒ τ

      open Constructors _◆_

      field
        _·ˢ_ : App
        fixˢ : Fix
        zˢ        : Z
        sˢ        : S
        caseNatˢ  : CaseNat
        nilˢ      : Nil
        _::ˢ_     : Cons
        caseListˢ : CaseList

      ⟦_⟧ : ∀ {Δ Γ σ} -> Γ ⊢ σ -> Δ ⊢* Γ -> Δ ◆ σ
      ⟦ var v ⟧ ρ = embˢ (lookupᵉ v ρ)
      ⟦ ƛ b   ⟧ ρ = lamˢ λ ι x -> ⟦ b ⟧ (renᵉ ι ρ ▷ x)
      ⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ·ˢ ⟦ x ⟧ ρ
      ⟦ fix f ⟧ ρ = fixˢ (⟦ f ⟧ ρ)
      ⟦ z               ⟧ ρ = zˢ
      ⟦ s n             ⟧ ρ = sˢ (⟦ n ⟧ ρ)
      ⟦ caseNat  n  y g ⟧ ρ = caseNatˢ  (⟦ n  ⟧ ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)
      ⟦ nil             ⟧ ρ = nilˢ
      ⟦ x :: xs         ⟧ ρ = ⟦ x ⟧ ρ ::ˢ ⟦ xs ⟧ ρ
      ⟦ caseList xs y g ⟧ ρ = caseListˢ (⟦ xs ⟧ ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)

      eval : _⊢_ ∸> _◆_
      eval t = ⟦ t ⟧ idᵉ
