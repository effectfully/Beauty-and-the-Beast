module SC.Build where

open import SC.Basic
open import SC.NF
open import SC.Semantics
open import SC.NbE

infix 4 _⊢ᵘⁿᵉ_

module Infinite Tag where
  infix  4 _⊢∞_
  infixr 3 ƛⁱ_
  infixl 6 _·ⁱ_
  infixr 5 _::ⁱ_

  data _⊢∞_ : Links

  open Constructors _⊢∞_

  data _⊢∞_ where
    varⁱ : Var
    ƛⁱ_  : Lam
    _·ⁱ_ : App
    zⁱ        : Z
    sⁱ        : S
    caseNatⁱ  : CaseNat
    nilⁱ      : Nil
    _::ⁱ_     : Cons
    caseListⁱ : CaseList
    checkpoint : ∀ {Γ σ} -> Tag -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ
    
  ⟨_⟩_⊢∞_ = _⊢∞_
open Infinite public using (⟨_⟩_⊢∞_)

data _⊢ᵘⁿᵉ_ : Links

open ConstructorsMutual _⊢ᵘⁿᵉ_ _⊢ⁿᶠ_

data _⊢ᵘⁿᵉ_ where
  varᵘⁿᵉ : Var
  _·ᵘⁿᵉ_ : App
  caseNatᵘⁿᵉ  : CaseNat
  caseListᵘⁿᵉ : CaseList

module _ where
  private module I = Infinite

  map∞ : ∀ {A B} -> (A -> B) -> ⟨ A ⟩_⊢∞_ ∸> ⟨ B ⟩_⊢∞_
  map∞ h (I.varⁱ v) = I.varⁱ v
  map∞ h (I.ƛⁱ b)   = I.ƛⁱ (map∞ h b)
  map∞ h (f I.·ⁱ x) = map∞ h f I.·ⁱ map∞ h x
  map∞ h  I.zⁱ                 = I.zⁱ
  map∞ h (I.sⁱ n)              = I.sⁱ (map∞ h n)
  map∞ h (I.caseNatⁱ   n  y g) = I.caseNatⁱ  (map∞ h n)  (map∞ h y) (map∞ h g)
  map∞ h  I.nilⁱ               = I.nilⁱ
  map∞ h (x I.::ⁱ xs)          = map∞ h x I.::ⁱ map∞ h xs
  map∞ h (I.caseListⁱ  xs y g) = I.caseListⁱ (map∞ h xs) (map∞ h y) (map∞ h g)
  map∞ h (I.checkpoint t n i) = I.checkpoint (h t) n (♯ map∞ h (♭ i))

embᵘⁿᵉ : _⊢ᵘⁿᵉ_ ∸> _⊢_
embᵘⁿᵉ (varᵘⁿᵉ v) = var v
embᵘⁿᵉ (f ·ᵘⁿᵉ x) = embᵘⁿᵉ f · embⁿᶠ x
embᵘⁿᵉ (caseNatᵘⁿᵉ  n  y g) = caseNat  (embᵘⁿᵉ n)  (embⁿᶠ y) (embⁿᶠ g)
embᵘⁿᵉ (caseListᵘⁿᵉ xs y g) = caseList (embᵘⁿᵉ xs) (embⁿᶠ y) (embⁿᶠ g)

data Clauses Γ : Type -> Type -> Set where
  natᶜ  : ∀ {τ}   -> Γ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ nat ⇒ τ        -> Clauses Γ  nat     τ
  listᶜ : ∀ {σ τ} -> Γ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ list σ ⇒ τ -> Clauses Γ (list σ) τ

recreate : ∀ {Γ σ τ} -> Γ ⊢ᵘⁿᵉ σ -> Clauses Γ σ τ -> Γ ⊢ᵘⁿᵉ τ
recreate n  (natᶜ  y g) = caseNatᵘⁿᵉ  n  y g
recreate xs (listᶜ y g) = caseListᵘⁿᵉ xs y g

open Kripkable record
  { _∙_  = _⊢_
  ; varˢ = var
  }

kripke : ∀ {Γ σ τ} -> Clauses Γ σ τ -> Kripke Γ σ τ
kripke (natᶜ  y g) ι n  = caseNat  n  (renᵗ ι (embⁿᶠ y)) (renᵗ ι (embⁿᶠ g))
kripke (listᶜ y g) ι xs = caseList xs (renᵗ ι (embⁿᶠ y)) (renᵗ ι (embⁿᶠ g))

data Perforate Γ τ : Set where
  before : Perforate Γ τ
  now    : ∀ {σ} -> Γ ⊢ᵘⁿᵉ base σ -> Kripke Γ (base σ) τ -> Perforate Γ τ

compᵖ : ∀ {Γ τ ν} -> Perforate Γ ν -> Kripke Γ τ ν -> Perforate Γ τ -> Perforate Γ ν
compᵖ p k₂  before    = p
compᵖ p k₂ (now t k₁) = now t (k₂ ∘ᵏ k₁)

mapᵖ : ∀ {Γ τ ν} -> Kripke Γ τ ν -> Perforate Γ τ -> Perforate Γ ν
mapᵖ = compᵖ before

perforate : _⊢ᵘⁿᵉ_ ∸> Perforate
perforate (varᵘⁿᵉ v) = before
perforate (f ·ᵘⁿᵉ x) = mapᵖ (λ ι f' -> f' · renᵗ ι (embⁿᶠ x)) (perforate f)
perforate (caseNatᵘⁿᵉ  n  y g) = compᵖ (now n  f) f (perforate n)  where f = kripke (natᶜ  y g)
perforate (caseListᵘⁿᵉ xs y g) = compᵖ (now xs f) f (perforate xs) where f = kripke (listᶜ y g)

unroll : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ ⊎ Γ ⊢ᵘⁿᵉ σ
unroll (varⁿᵉ v) = inj₂ (varᵘⁿᵉ v)
unroll (f ·ⁿᵉ x) = smap (_· embⁿᶠ x) (_·ᵘⁿᵉ x) (unroll f)
unroll (fixⁿᵉ f) = inj₁ (embⁿᶠ f · embⁿᵉ (fixⁿᵉ f))
unroll (caseNatⁿᵉ  n  y g) = smap (λ n'  -> caseNat  n'  (embⁿᶠ y) (embⁿᶠ g))
                                  (λ n'  -> caseNatᵘⁿᵉ  n'  y g)
                                  (unroll n)
unroll (caseListⁿᵉ xs y g) = smap (λ xs' -> caseList xs' (embⁿᶠ y) (embⁿᶠ g))
                                  (λ xs' -> caseListᵘⁿᵉ xs' y g)
                                  (unroll xs)

open Infinite ⊤

check : ∀ {Γ σ} -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ 
check = checkpoint _

{-# TERMINATING #-}
mutual
  revert : ∀ {Γ σ τ} -> Γ ⊢ᵘⁿᵉ σ -> Clauses Γ σ τ -> Γ ⊢∞ τ
  revert n c with mapᵖ (kripke c) (perforate n)
  revert n c | before         with c
  ... | natᶜ  y g = caseNatⁱ  (buildᵘⁿᵉ n) (buildⁿᶠ y) (buildⁿᶠ g)
  ... | listᶜ y g = caseListⁱ (buildᵘⁿᵉ n) (buildⁿᶠ y) (buildⁿᶠ g)
  revert n c | now {σ} e fill with λ {Δ} (ι : _ ⊆ Δ) -> build ∘ fill ι
  ... | go with σ
  ... | bnat    = caseNatⁱ  (buildᵘⁿᵉ e)
                            (go stop z)
                            (ƛⁱ (go (skip stop) (s (var vz))))
  ... | blist _ = caseListⁱ (buildᵘⁿᵉ e)
                            (go stop nil)
                            (ƛⁱ ƛⁱ (go (skip (skip stop)) (var (vs vz) :: var vz)))

  check-revert : ∀ {Γ σ τ} -> Γ ⊢ᵘⁿᵉ σ -> Clauses Γ σ τ -> Γ ⊢∞ τ
  check-revert n c = check (embᵘⁿᵉ (recreate n c)) (♯ revert n c)

  buildᵘⁿᵉ : _⊢ᵘⁿᵉ_ ∸> _⊢∞_
  buildᵘⁿᵉ (varᵘⁿᵉ v) = varⁱ v
  buildᵘⁿᵉ (f ·ᵘⁿᵉ x) = buildᵘⁿᵉ f ·ⁱ buildⁿᶠ x
  buildᵘⁿᵉ (caseNatᵘⁿᵉ  n  y g) = check-revert n  (natᶜ  y g)
  buildᵘⁿᵉ (caseListᵘⁿᵉ xs y g) = check-revert xs (listᶜ y g)

  buildⁿᵉ : _⊢ⁿᵉ_ ∸> _⊢∞_
  buildⁿᵉ n = [ (λ n' -> check (embⁿᵉ n) (♯ build n')) , buildᵘⁿᵉ ] (unroll n)

  buildⁿᶠ : _⊢ⁿᶠ_ ∸> _⊢∞_
  buildⁿᶠ (neⁿᶠ n) = buildⁿᵉ n
  buildⁿᶠ (ƛⁿᶠ b)  = ƛⁱ (buildⁿᶠ b)
  buildⁿᶠ  zⁿᶠ        = zⁱ
  buildⁿᶠ (sⁿᶠ n)     = {- check (embⁿᶠ (sⁿᶠ n)) $ ♯ -} sⁱ (buildⁿᶠ n)
  buildⁿᶠ  nilⁿᶠ      = nilⁱ
  buildⁿᶠ (x ::ⁿᶠ xs) = buildⁿᶠ x ::ⁱ buildⁿᶠ xs

  build : _⊢_ ∸> _⊢∞_
  build = buildⁿᶠ ∘ nf
