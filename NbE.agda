module SC.NbE where

open import Function

open import SC.Basic

infix 3 _⊢ⁿᵉ_ _⊢ⁿᶠ_ _⊢ˢⁿᵉ_ _⊢ˢⁿᶠ_ _↦_
infixl 6 _·ⁿᵉ_ _·ˢⁿᵉ_ _·ˢⁿᶠ_
infixr 5 _::ⁿᶠ_ _::ˢⁿᶠ_

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ
    fixⁿᵉ : ∀ {σ}   -> Γ ⊢ⁿᶠ σ ⇒ σ -> Γ ⊢ⁿᵉ σ
    caseNatⁿᵉ  : ∀ {σ}   -> Γ ⊢ⁿᵉ nat    -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᶠ nat ⇒ σ        -> Γ ⊢ⁿᵉ σ
    caseListⁿᵉ : ∀ {σ τ} -> Γ ⊢ⁿᵉ list σ -> Γ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : ∀ {σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ  : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ
    zⁿᶠ    :          Γ ⊢ⁿᶠ nat
    sⁿᶠ    :          Γ ⊢ⁿᶠ nat    -> Γ ⊢ⁿᶠ nat
    nilⁿᶠ  : ∀ {σ} -> Γ ⊢ⁿᶠ list σ
    _::ⁿᶠ_ : ∀ {σ} -> Γ ⊢ⁿᶠ σ      -> Γ ⊢ⁿᶠ list σ -> Γ ⊢ⁿᶠ list σ

mutual
  embⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x
  embⁿᵉ (fixⁿᵉ f) = fix (embⁿᶠ f)
  embⁿᵉ (caseNatⁿᵉ  n  y g) = caseNat  (embⁿᵉ n)  (embⁿᶠ y) (embⁿᶠ g)
  embⁿᵉ (caseListⁿᵉ xs y g) = caseList (embⁿᵉ xs) (embⁿᶠ y) (embⁿᶠ g)

  embⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  embⁿᶠ (neⁿᶠ x) = embⁿᵉ x
  embⁿᶠ (ƛⁿᶠ b)  = ƛ (embⁿᶠ b)
  embⁿᶠ  zⁿᶠ        = z
  embⁿᶠ (sⁿᶠ n)     = s (embⁿᶠ n)
  embⁿᶠ  nilⁿᶠ      = nil
  embⁿᶠ (x ::ⁿᶠ xs) = embⁿᶠ x :: embⁿᶠ xs

mutual
  data _⊢ˢⁿᵉ_ Γ : Type -> Set where
    varˢⁿᵉ    : ∀ {σ}   -> σ ∈ Γ        -> Γ ⊢ˢⁿᵉ σ
    _·ˢⁿᵉ_    : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᵉ τ
    fixˢⁿᵉ    : ∀ {σ}   -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᵉ σ
    weakenˢⁿᵉ : ∀ {Ω σ} -> Ω ⊆ Γ        -> Ω ⊢ˢⁿᵉ σ -> Γ ⊢ˢⁿᵉ σ
    caseNatˢⁿᵉ  : ∀ {σ}   -> Γ ⊢ˢⁿᵉ nat    -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ nat ⇒ σ        -> Γ ⊢ˢⁿᵉ σ
    caseListˢⁿᵉ : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ list σ -> Γ ⊢ˢⁿᶠ τ -> Γ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ˢⁿᵉ τ

  data _⊢ˢⁿᶠ_ Γ : Type -> Set where
    neˢⁿᶠ     : ∀ {σ}     ->  Γ ⊢ˢⁿᵉ σ  -> Γ ⊢ˢⁿᶠ σ
    ƛˢⁿᶠ      : ∀ {Ω σ τ} ->  Ω ▻ σ ⊢ τ -> Ω ↦ Γ    -> Γ ⊢ˢⁿᶠ σ ⇒ τ
    weakenˢⁿᶠ : ∀ {Ω σ}   ->  Ω ⊆ Γ     -> Ω ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ σ
    zˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat
    sˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat    -> Γ ⊢ˢⁿᶠ nat
    nilˢⁿᶠ  : ∀ {σ} -> Γ ⊢ˢⁿᶠ list σ
    _::ˢⁿᶠ_ : ∀ {σ} -> Γ ⊢ˢⁿᶠ σ      -> Γ ⊢ˢⁿᶠ list σ -> Γ ⊢ˢⁿᶠ list σ

  data _↦_ : Con -> Con -> Set where
    Ø         : ∀ {Δ}     -> ε ↦ Δ
    _▷_       : ∀ {Ω Δ σ} -> Ω ↦ Δ -> Δ ⊢ˢⁿᶠ σ -> Ω ▻ σ ↦ Δ
    weakenᵉⁿᵛ : ∀ {Ω Γ Δ} -> Γ ⊆ Δ -> Ω ↦ Γ    -> Ω ↦ Δ

varˢⁿᶠ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ˢⁿᶠ σ
varˢⁿᶠ = neˢⁿᶠ ∘ varˢⁿᵉ

fixˢⁿᶠ : ∀ {Γ σ} -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᶠ σ
fixˢⁿᶠ = neˢⁿᶠ ∘ fixˢⁿᵉ

lookupᵉⁿᵛ : ∀ {Γ Δ Θ σ} -> Δ ⊆ Θ -> σ ∈ Γ -> Γ ↦ Δ -> Θ ⊢ˢⁿᶠ σ
lookupᵉⁿᵛ φ  vz    (ρ ▷ y)         = weakenˢⁿᶠ φ y
lookupᵉⁿᵛ φ (vs v) (ρ ▷ y)         = lookupᵉⁿᵛ  φ         v ρ
lookupᵉⁿᵛ φ  v     (weakenᵉⁿᵛ ψ ρ) = lookupᵉⁿᵛ (φ ∘ˢᵘᵇ ψ) v ρ

{-# TERMINATING #-}
⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> Δ ⊢ˢⁿᶠ σ

applyˢⁿᶠ : ∀ {Γ Δ σ τ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ σ ⇒ τ -> Δ ⊢ˢⁿᶠ σ -> Δ ⊢ˢⁿᶠ τ
applyˢⁿᶠ φ (neˢⁿᶠ f)       x = neˢⁿᶠ (weakenˢⁿᵉ φ f ·ˢⁿᵉ x)
applyˢⁿᶠ φ (ƛˢⁿᶠ b ρ)      x = ⟦ b ⟧ (weakenᵉⁿᵛ φ ρ ▷ x)
applyˢⁿᶠ φ (weakenˢⁿᶠ ψ f) x = applyˢⁿᶠ (φ ∘ˢᵘᵇ ψ) f x

_·ˢⁿᶠ_ : ∀ {Γ σ τ} -> Γ ⊢ˢⁿᶠ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ τ
_·ˢⁿᶠ_ = applyˢⁿᶠ stop

caseNatˢⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ nat -> Δ ⊢ˢⁿᶠ σ -> Δ ⊢ˢⁿᶠ nat ⇒ σ -> Δ ⊢ˢⁿᶠ σ
caseNatˢⁿᶠ φ (neˢⁿᶠ n)       y g = neˢⁿᶠ (caseNatˢⁿᵉ (weakenˢⁿᵉ φ n) y g)
caseNatˢⁿᶠ φ  zˢⁿᶠ           y g = y
caseNatˢⁿᶠ φ (sˢⁿᶠ n)        y g = g ·ˢⁿᶠ weakenˢⁿᶠ φ n
caseNatˢⁿᶠ φ (weakenˢⁿᶠ ψ n) y g = caseNatˢⁿᶠ (φ ∘ˢᵘᵇ ψ) n y g

caseListˢⁿᶠ : ∀ {Γ Δ σ τ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ list σ -> Δ ⊢ˢⁿᶠ τ -> Δ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Δ ⊢ˢⁿᶠ τ
caseListˢⁿᶠ φ (neˢⁿᶠ xs)       y g = neˢⁿᶠ (caseListˢⁿᵉ (weakenˢⁿᵉ φ xs) y g)
caseListˢⁿᶠ φ  nilˢⁿᶠ          y g = y
caseListˢⁿᶠ φ (x ::ˢⁿᶠ xs)     y g = g ·ˢⁿᶠ weakenˢⁿᶠ φ x ·ˢⁿᶠ weakenˢⁿᶠ φ xs
caseListˢⁿᶠ φ (weakenˢⁿᶠ ψ xs) y g = caseListˢⁿᶠ (φ ∘ˢᵘᵇ ψ) xs y g

⟦ var v ⟧ ρ = lookupᵉⁿᵛ stop v ρ
⟦ ƛ b   ⟧ ρ = ƛˢⁿᶠ b ρ
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ·ˢⁿᶠ ⟦ x ⟧ ρ
⟦ fix f ⟧ ρ = fixˢⁿᶠ (⟦ f ⟧ ρ)
⟦ z               ⟧ ρ = zˢⁿᶠ
⟦ s n             ⟧ ρ = sˢⁿᶠ (⟦ n ⟧ ρ)
⟦ caseNat  n  y g ⟧ ρ = caseNatˢⁿᶠ  stop (⟦ n ⟧  ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)
⟦ nil             ⟧ ρ = nilˢⁿᶠ
⟦ x :: xs         ⟧ ρ = ⟦ x ⟧ ρ ::ˢⁿᶠ ⟦ xs ⟧ ρ
⟦ caseList xs y g ⟧ ρ = caseListˢⁿᶠ stop (⟦ xs ⟧ ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)

{-# TERMINATING #-}
mutual
  quoteⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  quoteⁿᵉ φ (varˢⁿᵉ v)      = varⁿᵉ (weakenᵛᵃʳ φ v)
  quoteⁿᵉ φ (f ·ˢⁿᵉ x)      = quoteⁿᵉ φ f ·ⁿᵉ quoteⁿᶠ φ x
  quoteⁿᵉ φ (fixˢⁿᵉ f)      = fixⁿᵉ (quoteⁿᶠ φ f)
  quoteⁿᵉ φ (weakenˢⁿᵉ ψ x) = quoteⁿᵉ (φ ∘ˢᵘᵇ ψ) x
  quoteⁿᵉ φ (caseNatˢⁿᵉ  n  y g) = caseNatⁿᵉ  (quoteⁿᵉ φ n)  (quoteⁿᶠ φ y) (quoteⁿᶠ φ g)
  quoteⁿᵉ φ (caseListˢⁿᵉ xs y g) = caseListⁿᵉ (quoteⁿᵉ φ xs) (quoteⁿᶠ φ y) (quoteⁿᶠ φ g)

  quoteⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  quoteⁿᶠ φ (neˢⁿᶠ x)       = neⁿᶠ (quoteⁿᵉ φ x)
  quoteⁿᶠ φ (ƛˢⁿᶠ b ρ)      = ƛⁿᶠ (quoteⁿᶠ (keep φ) (⟦ b ⟧ (weakenᵉⁿᵛ top ρ ▷ varˢⁿᶠ vz)))
  quoteⁿᶠ φ (weakenˢⁿᶠ ψ x) = quoteⁿᶠ (φ ∘ˢᵘᵇ ψ) x
  quoteⁿᶠ φ  zˢⁿᶠ        = zⁿᶠ
  quoteⁿᶠ φ (sˢⁿᶠ x)     = sⁿᶠ (quoteⁿᶠ φ x)
  quoteⁿᶠ φ  nilˢⁿᶠ      = nilⁿᶠ
  quoteⁿᶠ φ (x ::ˢⁿᶠ xs) = quoteⁿᶠ φ x ::ⁿᶠ quoteⁿᶠ φ xs

idᵉⁿᵛ : ∀ {Γ} -> Γ ↦ Γ
idᵉⁿᵛ {ε}     = Ø
idᵉⁿᵛ {Γ ▻ σ} = weakenᵉⁿᵛ top idᵉⁿᵛ ▷ varˢⁿᶠ vz

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm x = embⁿᶠ (quoteⁿᶠ stop (⟦ x ⟧ idᵉⁿᵛ))
