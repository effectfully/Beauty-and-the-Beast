{-# OPTIONS --no-positivity-check #-}

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
    ne  : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ
    zⁿᶠ    :          Γ ⊢ⁿᶠ nat
    sⁿᶠ    :          Γ ⊢ⁿᶠ nat    -> Γ ⊢ⁿᶠ nat
    nilⁿᶠ  : ∀ {σ} -> Γ ⊢ⁿᶠ list σ
    _::ⁿᶠ_ : ∀ {σ} -> Γ ⊢ⁿᶠ σ      -> Γ ⊢ⁿᶠ list σ -> Γ ⊢ⁿᶠ list σ

mutual
  fromⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  fromⁿᵉ (varⁿᵉ v) = var v
  fromⁿᵉ (f ·ⁿᵉ x) = fromⁿᵉ f · fromⁿᶠ x
  fromⁿᵉ (fixⁿᵉ f) = fix (fromⁿᶠ f)
  fromⁿᵉ (caseNatⁿᵉ  n  y g) = caseNat  (fromⁿᵉ n)  (fromⁿᶠ y) (fromⁿᶠ g)
  fromⁿᵉ (caseListⁿᵉ xs y g) = caseList (fromⁿᵉ xs) (fromⁿᶠ y) (fromⁿᶠ g)

  fromⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  fromⁿᶠ (ne x)  = fromⁿᵉ x
  fromⁿᶠ (ƛⁿᶠ b) = ƛ (fromⁿᶠ b)
  fromⁿᶠ  zⁿᶠ        = z
  fromⁿᶠ (sⁿᶠ n)     = s (fromⁿᶠ n)
  fromⁿᶠ  nilⁿᶠ      = nil
  fromⁿᶠ (x ::ⁿᶠ xs) = fromⁿᶠ x :: fromⁿᶠ xs

mutual
  data _⊢ˢⁿᵉ_ Γ : Type -> Set where
    varˢⁿᵉ    : ∀ {σ}   -> σ ∈ Γ        -> Γ ⊢ˢⁿᵉ σ
    _·ˢⁿᵉ_    : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᵉ τ
    fixˢⁿᵉ    : ∀ {σ}   -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᵉ σ
    weakenˢⁿᵉ : ∀ {Ω σ} -> Ω ⊆ Γ        -> Ω ⊢ˢⁿᵉ σ -> Γ ⊢ˢⁿᵉ σ
    caseNatˢⁿᵉ  : ∀ {σ}   -> Γ ⊢ˢⁿᵉ nat    -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ nat ⇒ σ        -> Γ ⊢ˢⁿᵉ σ
    caseListˢⁿᵉ : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ list σ -> Γ ⊢ˢⁿᶠ τ -> Γ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ˢⁿᵉ τ

  data _⊢ˢⁿᶠ_ Γ : Type -> Set where
    neˢ       : ∀ {σ}   ->  Γ ⊢ˢⁿᵉ σ                                -> Γ ⊢ˢⁿᶠ σ
    ƛˢⁿᶠ      : ∀ {σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ˢⁿᶠ σ -> Δ ⊢ˢⁿᶠ τ) -> Γ ⊢ˢⁿᶠ σ ⇒ τ
    weakenˢⁿᶠ : ∀ {Ω σ} ->  Ω ⊆ Γ                                   -> Ω ⊢ˢⁿᶠ σ     -> Γ ⊢ˢⁿᶠ σ
    zˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat
    sˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat    -> Γ ⊢ˢⁿᶠ nat
    nilˢⁿᶠ  : ∀ {σ} -> Γ ⊢ˢⁿᶠ list σ
    _::ˢⁿᶠ_ : ∀ {σ} -> Γ ⊢ˢⁿᶠ σ      -> Γ ⊢ˢⁿᶠ list σ -> Γ ⊢ˢⁿᶠ list σ

varˢⁿᶠ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ˢⁿᶠ σ
varˢⁿᶠ = neˢ ∘ varˢⁿᵉ

fixˢⁿᶠ : ∀ {Γ σ} -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᶠ σ
fixˢⁿᶠ = neˢ ∘ fixˢⁿᵉ

applyˢⁿᶠ : ∀ {Γ Δ σ τ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ σ ⇒ τ -> Δ ⊢ˢⁿᶠ σ -> Δ ⊢ˢⁿᶠ τ
applyˢⁿᶠ φ (neˢ f)         x = neˢ (weakenˢⁿᵉ φ f ·ˢⁿᵉ x)
applyˢⁿᶠ φ (ƛˢⁿᶠ f)        x = f φ x
applyˢⁿᶠ φ (weakenˢⁿᶠ ψ f) x = applyˢⁿᶠ (φ ∘ˢᵘᵇ ψ) f x

_·ˢⁿᶠ_ : ∀ {Γ σ τ} -> Γ ⊢ˢⁿᶠ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ τ
_·ˢⁿᶠ_ = applyˢⁿᶠ stop

caseNatˢⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ nat -> Δ ⊢ˢⁿᶠ σ -> Δ ⊢ˢⁿᶠ nat ⇒ σ -> Δ ⊢ˢⁿᶠ σ
caseNatˢⁿᶠ φ (neˢ n)         y g = neˢ (caseNatˢⁿᵉ (weakenˢⁿᵉ φ n) y g)
caseNatˢⁿᶠ φ  zˢⁿᶠ           y g = y
caseNatˢⁿᶠ φ (sˢⁿᶠ n)        y g = g ·ˢⁿᶠ weakenˢⁿᶠ φ n
caseNatˢⁿᶠ φ (weakenˢⁿᶠ ψ n) y g = caseNatˢⁿᶠ (φ ∘ˢᵘᵇ ψ) n y g

caseListˢⁿᶠ : ∀ {Γ Δ σ τ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ list σ -> Δ ⊢ˢⁿᶠ τ -> Δ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Δ ⊢ˢⁿᶠ τ
caseListˢⁿᶠ φ (neˢ xs)         y g = neˢ (caseListˢⁿᵉ (weakenˢⁿᵉ φ xs) y g)
caseListˢⁿᶠ φ  nilˢⁿᶠ          y g = y
caseListˢⁿᶠ φ (x ::ˢⁿᶠ xs)     y g = g ·ˢⁿᶠ weakenˢⁿᶠ φ x ·ˢⁿᶠ weakenˢⁿᶠ φ xs
caseListˢⁿᶠ φ (weakenˢⁿᶠ ψ xs) y g = caseListˢⁿᶠ (φ ∘ˢᵘᵇ ψ) xs y g

data _↦_ : Con -> Con -> Set where
  Ø         : ∀ {Δ}     -> ε ↦ Δ
  _▷_       : ∀ {Ω Δ σ} -> Ω ↦ Δ -> Δ ⊢ˢⁿᶠ σ -> Ω ▻ σ ↦ Δ
  weakenᵉⁿᵛ : ∀ {Ω Γ Δ} -> Γ ⊆ Δ -> Ω ↦ Γ    -> Ω ↦ Δ

lookupᵉⁿᵛ : ∀ {Γ Δ Θ σ} -> Δ ⊆ Θ -> σ ∈ Γ -> Γ ↦ Δ -> Θ ⊢ˢⁿᶠ σ
lookupᵉⁿᵛ φ  vz    (ρ ▷ y)         = weakenˢⁿᶠ φ y
lookupᵉⁿᵛ φ (vs v) (ρ ▷ y)         = lookupᵉⁿᵛ  φ         v ρ
lookupᵉⁿᵛ φ  v     (weakenᵉⁿᵛ ψ ρ) = lookupᵉⁿᵛ (φ ∘ˢᵘᵇ ψ) v ρ

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> Δ ⊢ˢⁿᶠ σ
⟦ var v ⟧ ρ = lookupᵉⁿᵛ stop v ρ
⟦ ƛ b   ⟧ ρ = ƛˢⁿᶠ λ ψ y -> ⟦ b ⟧ (weakenᵉⁿᵛ ψ ρ ▷ y)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ·ˢⁿᶠ ⟦ x ⟧ ρ
⟦ fix f ⟧ ρ = fixˢⁿᶠ (⟦ f ⟧ ρ)
⟦ z               ⟧ ρ = zˢⁿᶠ
⟦ s n             ⟧ ρ = sˢⁿᶠ (⟦ n ⟧ ρ)
⟦ caseNat  n  y g ⟧ ρ = caseNatˢⁿᶠ  stop (⟦ n ⟧  ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)
⟦ nil             ⟧ ρ = nilˢⁿᶠ
⟦ x :: xs         ⟧ ρ = ⟦ x ⟧ ρ ::ˢⁿᶠ ⟦ xs ⟧ ρ
⟦ caseList xs y g ⟧ ρ = caseListˢⁿᶠ stop (⟦ xs ⟧ ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)

mutual
  quoteⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  quoteⁿᵉ φ (varˢⁿᵉ v)      = varⁿᵉ (weakenᵛᵃʳ φ v)
  quoteⁿᵉ φ (f ·ˢⁿᵉ x)      = quoteⁿᵉ φ f ·ⁿᵉ quoteⁿᶠ φ x
  quoteⁿᵉ φ (fixˢⁿᵉ f)      = fixⁿᵉ (quoteⁿᶠ φ f)
  quoteⁿᵉ φ (weakenˢⁿᵉ ψ x) = quoteⁿᵉ (φ ∘ˢᵘᵇ ψ) x
  quoteⁿᵉ φ (caseNatˢⁿᵉ  n  y g) = caseNatⁿᵉ  (quoteⁿᵉ φ n)  (quoteⁿᶠ φ y) (quoteⁿᶠ φ g)
  quoteⁿᵉ φ (caseListˢⁿᵉ xs y g) = caseListⁿᵉ (quoteⁿᵉ φ xs) (quoteⁿᶠ φ y) (quoteⁿᶠ φ g)

  quoteⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ˢⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  quoteⁿᶠ φ (neˢ x)         = ne (quoteⁿᵉ φ x)
  quoteⁿᶠ φ (ƛˢⁿᶠ f)        = ƛⁿᶠ (quoteⁿᶠ (keep φ) (f top (varˢⁿᶠ vz)))
  quoteⁿᶠ φ (weakenˢⁿᶠ ψ x) = quoteⁿᶠ (φ ∘ˢᵘᵇ ψ) x
  quoteⁿᶠ φ  zˢⁿᶠ        = zⁿᶠ
  quoteⁿᶠ φ (sˢⁿᶠ x)     = sⁿᶠ (quoteⁿᶠ φ x)
  quoteⁿᶠ φ  nilˢⁿᶠ      = nilⁿᶠ
  quoteⁿᶠ φ (x ::ˢⁿᶠ xs) = quoteⁿᶠ φ x ::ⁿᶠ quoteⁿᶠ φ xs

idᵉⁿᵛ : ∀ {Γ} -> Γ ↦ Γ
idᵉⁿᵛ {ε}     = Ø
idᵉⁿᵛ {Γ ▻ σ} = weakenᵉⁿᵛ top idᵉⁿᵛ ▷ varˢⁿᶠ vz

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm x = fromⁿᶠ (quoteⁿᶠ stop (⟦ x ⟧ idᵉⁿᵛ))
