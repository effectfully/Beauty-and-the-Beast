module SC.NF where

open import SC.Basic

infix  4 _⊢ⁿᵉ_ _⊢ⁿᶠ_
infixl 6 _·ⁿᵉ_
infixr 5 _::ⁿᶠ_

data _⊢ⁿᵉ_ : Links
data _⊢ⁿᶠ_ : Links

open ConstructorsMutual _⊢ⁿᵉ_ _⊢ⁿᶠ_

data _⊢ⁿᵉ_ where
  varⁿᵉ : Var
  _·ⁿᵉ_ : App
  fixⁿᵉ : Fix
  caseNatⁿᵉ  : CaseNat
  caseListⁿᵉ : CaseList

data _⊢ⁿᶠ_ where
  neⁿᶠ : Ne
  ƛⁿᶠ  : Lam
  zⁿᶠ    : Z
  sⁿᶠ    : S
  nilⁿᶠ  : Nil
  _::ⁿᶠ_ : Cons

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
