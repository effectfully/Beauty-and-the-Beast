module SC.Semantics where

open import SC.Basic

record EnvKit : Set₁ where
  infix 4 _∙_

  field
    _∙_  : Links
    varᵏ : _∋_ ∸> _∙_
    renᵏ : Renames _∙_

record SemKit (envKit : EnvKit) : Set₁ where
  open EnvKit envKit

  infix  4 _◆_
  infixl 6 _·ˢ_
  infixr 5 _::ˢ_

  field
    _◆_  : Links
    embˢ : _∙_ ∸> _◆_
    lamˢ : ∀ {Γ σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ∙ σ -> Δ ◆ τ) -> Γ ◆ σ ⇒ τ
    _·ˢ_ : ∀ {Γ σ τ} -> Γ ◆ σ ⇒ τ -> Γ ◆ σ -> Γ ◆ τ
    fixˢ : ∀ {Γ σ}   -> Γ ◆ σ ⇒ σ -> Γ ◆ σ
    zˢ        : ∀ {Γ}     -> Γ ◆ nat
    sˢ        : ∀ {Γ}     -> Γ ◆ nat    -> Γ ◆ nat
    caseNatˢ  : ∀ {Γ σ}   -> Γ ◆ nat    -> Γ ◆ σ      -> Γ ◆ nat ⇒ σ        -> Γ ◆ σ
    nilˢ      : ∀ {Γ σ}   -> Γ ◆ list σ
    _::ˢ_     : ∀ {Γ σ}   -> Γ ◆ σ      -> Γ ◆ list σ -> Γ ◆ list σ
    caseListˢ : ∀ {Γ σ τ} -> Γ ◆ list σ -> Γ ◆ τ      -> Γ ◆ σ ⇒ list σ ⇒ τ -> Γ ◆ τ

module Environment (envKit : EnvKit) where
  open EnvKit envKit public

  infix 4 _↦_

  data _↦_ : Con -> Con -> Set where
    Ø   : ∀ {Δ} -> ε ↦ Δ
    _▷_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> Δ ∙ σ -> Γ ▻ σ ↦ Δ

  lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Γ ↦ Δ -> Δ ∙ σ
  lookupᵉ  vz    (ρ ▷ x) = x
  lookupᵉ (vs v) (ρ ▷ x) = lookupᵉ v ρ

  renᵉ : ∀ {Γ Δ Ξ} -> Δ ⊆ Ξ -> Γ ↦ Δ -> Γ ↦ Ξ
  renᵉ ι  Ø      = Ø
  renᵉ ι (ρ ▷ x) = renᵉ ι ρ ▷ renᵏ ι x

  idᵉ : ∀ {Γ} -> Γ ↦ Γ
  idᵉ {ε}     = Ø
  idᵉ {Γ ▻ σ} = renᵉ top idᵉ ▷ varᵏ vz

module Semantics {envKit} (semKit : SemKit envKit) where
  open SemKit semKit      public
  open Environment envKit public

  ⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> Δ ◆ σ
  ⟦ var v ⟧ ρ = embˢ (lookupᵉ v ρ)
  ⟦ ƛ b   ⟧ ρ = lamˢ (λ ι x -> ⟦ b ⟧ (renᵉ ι ρ ▷ x))
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
