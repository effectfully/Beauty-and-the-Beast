{-# OPTIONS --no-positivity-check #-}

module SC.Illustrations.NoSubNbE where

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
    varˢⁿᵉ : ∀ {σ}   -> σ ∈ Γ        -> Γ ⊢ˢⁿᵉ σ
    _·ˢⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᵉ τ
    fixˢⁿᵉ : ∀ {σ}   -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᵉ σ
    caseNatˢⁿᵉ  : ∀ {σ}   -> Γ ⊢ˢⁿᵉ nat    -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ nat ⇒ σ        -> Γ ⊢ˢⁿᵉ σ
    caseListˢⁿᵉ : ∀ {σ τ} -> Γ ⊢ˢⁿᵉ list σ -> Γ ⊢ˢⁿᶠ τ -> Γ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ˢⁿᵉ τ

  data _⊢ˢⁿᶠ_ Γ : Type -> Set where
    neˢ  : ∀ {σ}   ->  Γ ⊢ˢⁿᵉ σ              -> Γ ⊢ˢⁿᶠ σ
    ƛˢⁿᶠ : ∀ {σ τ} -> (Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ τ) -> Γ ⊢ˢⁿᶠ σ ⇒ τ
    zˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat
    sˢⁿᶠ    :          Γ ⊢ˢⁿᶠ nat    -> Γ ⊢ˢⁿᶠ nat
    nilˢⁿᶠ  : ∀ {σ} -> Γ ⊢ˢⁿᶠ list σ
    _::ˢⁿᶠ_ : ∀ {σ} -> Γ ⊢ˢⁿᶠ σ      -> Γ ⊢ˢⁿᶠ list σ -> Γ ⊢ˢⁿᶠ list σ

varˢⁿᶠ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ⊢ˢⁿᶠ σ
varˢⁿᶠ = neˢ ∘ varˢⁿᵉ

fixˢⁿᶠ : ∀ {Γ σ} -> Γ ⊢ˢⁿᶠ σ ⇒ σ -> Γ ⊢ˢⁿᶠ σ
fixˢⁿᶠ = neˢ ∘ fixˢⁿᵉ

_·ˢⁿᶠ_ : ∀ {Γ σ τ} -> Γ ⊢ˢⁿᶠ σ ⇒ τ -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ τ
neˢ  f ·ˢⁿᶠ x = neˢ (f ·ˢⁿᵉ x)
ƛˢⁿᶠ f ·ˢⁿᶠ x = f x

caseNatˢⁿᶠ : ∀ {Γ σ} -> Γ ⊢ˢⁿᶠ nat -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ˢⁿᶠ nat ⇒ σ -> Γ ⊢ˢⁿᶠ σ
caseNatˢⁿᶠ (neˢ n)  y g = neˢ (caseNatˢⁿᵉ n y g)
caseNatˢⁿᶠ  zˢⁿᶠ    y g = y
caseNatˢⁿᶠ (sˢⁿᶠ n) y g = g ·ˢⁿᶠ n

caseListˢⁿᶠ : ∀ {Γ σ τ} -> Γ ⊢ˢⁿᶠ list σ -> Γ ⊢ˢⁿᶠ τ -> Γ ⊢ˢⁿᶠ σ ⇒ list σ ⇒ τ -> Γ ⊢ˢⁿᶠ τ
caseListˢⁿᶠ (neˢ xs)     y g = neˢ (caseListˢⁿᵉ xs y g)
caseListˢⁿᶠ  nilˢⁿᶠ      y g = y
caseListˢⁿᶠ (x ::ˢⁿᶠ xs) y g = g ·ˢⁿᶠ x ·ˢⁿᶠ xs

data _↦_ : Con -> Con -> Set where
  Ø   : ∀ {Δ}     -> ε ↦ Δ
  _▷_ : ∀ {Ω Δ σ} -> Ω ↦ Δ -> Δ ⊢ˢⁿᶠ σ -> Ω ▻ σ ↦ Δ

lookupᵉⁿᵛ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Γ ↦ Δ -> Δ ⊢ˢⁿᶠ σ
lookupᵉⁿᵛ  vz    (ρ ▷ y) = y
lookupᵉⁿᵛ (vs v) (ρ ▷ y) = lookupᵉⁿᵛ v ρ

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> Δ ⊢ˢⁿᶠ σ
⟦ var v ⟧ ρ = lookupᵉⁿᵛ v ρ
⟦ ƛ b   ⟧ ρ = ƛˢⁿᶠ λ y -> ⟦ b ⟧ (ρ ▷ y)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ ·ˢⁿᶠ ⟦ x ⟧ ρ
⟦ fix f ⟧ ρ = fixˢⁿᶠ (⟦ f ⟧ ρ)
⟦ z               ⟧ ρ = zˢⁿᶠ
⟦ s n             ⟧ ρ = sˢⁿᶠ (⟦ n ⟧ ρ)
⟦ caseNat  n  y g ⟧ ρ = caseNatˢⁿᶠ  (⟦ n ⟧  ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)
⟦ nil             ⟧ ρ = nilˢⁿᶠ
⟦ x :: xs         ⟧ ρ = ⟦ x ⟧ ρ ::ˢⁿᶠ ⟦ xs ⟧ ρ
⟦ caseList xs y g ⟧ ρ = caseListˢⁿᶠ (⟦ xs ⟧ ρ) (⟦ y ⟧ ρ) (⟦ g ⟧ ρ)

mutual
  quoteⁿᵉ : ∀ {Γ σ} -> Γ ⊢ˢⁿᵉ σ -> Γ ⊢ⁿᵉ σ
  quoteⁿᵉ (varˢⁿᵉ v) = varⁿᵉ v
  quoteⁿᵉ (f ·ˢⁿᵉ x) = quoteⁿᵉ f ·ⁿᵉ quoteⁿᶠ x
  quoteⁿᵉ (fixˢⁿᵉ f) = fixⁿᵉ (quoteⁿᶠ f)
  quoteⁿᵉ (caseNatˢⁿᵉ  n  y g) = caseNatⁿᵉ  (quoteⁿᵉ n)  (quoteⁿᶠ y) (quoteⁿᶠ g)
  quoteⁿᵉ (caseListˢⁿᵉ xs y g) = caseListⁿᵉ (quoteⁿᵉ xs) (quoteⁿᶠ y) (quoteⁿᶠ g)

  quoteⁿᶠ : ∀ {Γ σ} -> Γ ⊢ˢⁿᶠ σ -> Γ ⊢ⁿᶠ σ
  quoteⁿᶠ (neˢ x)  = ne (quoteⁿᵉ x)
  quoteⁿᶠ (ƛˢⁿᶠ f) = ƛⁿᶠ (quoteⁿᶠ {!f (varˢⁿᶠ vz)!}) -- oops
  quoteⁿᶠ  zˢⁿᶠ        = zⁿᶠ
  quoteⁿᶠ (sˢⁿᶠ x)     = sⁿᶠ (quoteⁿᶠ x)
  quoteⁿᶠ  nilˢⁿᶠ      = nilⁿᶠ
  quoteⁿᶠ (x ::ˢⁿᶠ xs) = quoteⁿᶠ x ::ⁿᶠ quoteⁿᶠ xs

postulate
  weakenᵉⁿᵛ : ∀ {Ω Γ Δ} -> Γ ⊆ Δ -> Ω ↦ Γ -> Ω ↦ Δ

idᵉⁿᵛ : ∀ {Γ} -> Γ ↦ Γ
idᵉⁿᵛ {ε}     = Ø
idᵉⁿᵛ {Γ ▻ σ} = weakenᵉⁿᵛ top idᵉⁿᵛ ▷ varˢⁿᶠ vz

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm x = fromⁿᶠ (quoteⁿᶠ (⟦ x ⟧ idᵉⁿᵛ))
