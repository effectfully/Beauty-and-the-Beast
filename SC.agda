module SC.SC where

open import SC.Basic
open import SC.Build

open import Data.String.Base as Name renaming (String to Name) hiding (toList; show)
open Infinite (Bool × Name)

-- {-# NO_ETA Σ #-} ?

infixl 6 _·_
infixr 5 _::_

_++ℕ_ : Name -> ℕ -> Name
n ++ℕ i = n Name.++ show i

data Spine : Set where
  varˢ  : Spine -- Just an approximation.
  ƛˢ_   : Spine -> Spine
  _·ˢ_  : Spine -> Spine -> Spine
  fixˢ_ : Spine -> Spine
  zˢ        : Spine
  sˢ        : Spine -> Spine
  caseNatˢ  : Spine -> Spine -> Spine -> Spine
  nilˢ      : Spine
  _::ˢ_     : Spine -> Spine -> Spine
  caseListˢ : Spine -> Spine -> Spine -> Spine

data Result : Set where
  var        : Name   -> Result
  lam        : Name   -> Result -> Result
  _·_        : Result -> Result -> Result
  Let_:=_In_ : Name   -> Result -> Result -> Result
  z        : Result
  s        : Result -> Result
  caseNat  : Result -> Result -> Result -> Result
  nil      : Result
  _::_     : Result -> Result -> Result
  caseList : Result -> Result -> Result -> Result

instance
  Eq-Spine : Eq Spine
  Eq-Spine = record { _==_ = _==ᵇ_ } where
    infixl 8 _==ᵇ_

    _==ᵇ_ : Spine -> Spine -> Bool
    varˢ     ==ᵇ varˢ     = true
    (ƛˢ x)   ==ᵇ (ƛˢ y)   = x ==ᵇ y
    (f ·ˢ x) ==ᵇ (g ·ˢ y) = f ==ᵇ g ∧ x ==ᵇ y
    (fixˢ f) ==ᵇ (fixˢ g) = f ==ᵇ g
    zˢ               ==ᵇ zˢ               = true
    sˢ n             ==ᵇ sˢ m             = n ==ᵇ m
    caseNatˢ  n  x f ==ᵇ caseNatˢ  m  y g = n  ==ᵇ m  ∧ x ==ᵇ y ∧ f ==ᵇ g
    nilˢ             ==ᵇ nilˢ             = true
    (x ::ˢ xs)       ==ᵇ (y ::ˢ ys)       = x ==ᵇ y ∧ xs ==ᵇ ys
    caseListˢ xs x f ==ᵇ caseListˢ ys y g = xs ==ᵇ ys ∧ x ==ᵇ y ∧ f ==ᵇ g
    _                ==ᵇ _                = false

spine : ∀ {Γ σ} -> Γ ⊢ σ -> Spine
spine (var v) = varˢ
spine (ƛ b)   = ƛˢ (spine b)
spine (f · x) = spine f ·ˢ spine x
spine (fix f) = fixˢ (spine f)
spine  z                = zˢ
spine (s n)             = sˢ (spine n)
spine (caseNat  n  y g) = caseNatˢ  (spine n)  (spine y) (spine g)
spine  nil              = nilˢ
spine (x :: xs)         = spine x ::ˢ spine xs
spine (caseList xs y g) = caseListˢ (spine xs) (spine y) (spine g)

{-# NON_TERMINATING #-}
scatter : ∀ {n Γ σ} -> Vec (Spine × Name) n -> Γ ⊢∞ σ -> List Name × Γ ⊢∞ σ 
scatter       ρ (varⁱ v) = return (varⁱ v)
scatter       ρ (ƛⁱ b)   = ƛⁱ_ <$> scatter ρ b
scatter       ρ (f ·ⁱ x) = _·ⁱ_ <$> scatter ρ f ⊛ scatter ρ x
scatter       ρ  zⁱ                = return zⁱ
scatter       ρ (sⁱ n)             = sⁱ <$> scatter ρ n
scatter       ρ (caseNatⁱ  n  y g) = caseNatⁱ  <$> scatter ρ n  ⊛ scatter ρ y ⊛ scatter ρ g
scatter       ρ  nilⁱ              = return nilⁱ
scatter       ρ (x ::ⁱ xs)         = _::ⁱ_ <$> scatter ρ x ⊛ scatter ρ xs
scatter       ρ (caseListⁱ xs y g) = caseListⁱ <$> scatter ρ xs ⊛ scatter ρ y ⊛ scatter ρ g
scatter {new} ρ (checkpoint _ t i) =
  maybe (λ rn' -> rn' ∷ [] , checkpoint (true , rn') t i)
        (case scatter ((et , rn) ∷ ρ) (♭ i) of λ{
            (ns , x') -> maybe (λ ns' -> ns' , checkpoint (false , rn) t (♯ x'))
                               (ns , x')
                               (deletem rn ns)
        })
        (lookup-for et (toList ρ))
  where
    et = spine t
    rn = "r" ++ℕ new

{-# NON_TERMINATING #-} -- Because `scatter' is non-terminating.
residualize : ∀ {Γ σ} -> Vec Name (lenᶜ Γ) -> Γ ⊢∞ σ -> Result
residualize ρ (varⁱ v) = var (lookup (∈-to-Fin v) ρ)
residualize ρ (ƛⁱ b)   = lam xn (residualize (xn ∷ ρ) b) where xn = "x" ++ℕ lenᵛ ρ
residualize ρ (f ·ⁱ x) = residualize ρ f · residualize ρ x
residualize ρ  zⁱ                = z
residualize ρ (sⁱ n)             = s (residualize ρ n)
residualize ρ (caseNatⁱ  n  y g) =
  caseNat  (residualize ρ n)  (residualize ρ y) (residualize ρ g)
residualize ρ  nilⁱ              = nil
residualize ρ (x ::ⁱ xs)         = residualize ρ x :: residualize ρ xs
residualize ρ (caseListⁱ xs y g) =
  caseList (residualize ρ xs) (residualize ρ y) (residualize ρ g)
residualize ρ (checkpoint (seen , rn) t i) =
  if seen then saturate rn else (Let rn := λ-abstract (residualize ρ (♭ i)) In saturate rn)
  where
    rs = lmap (flip lookup ρ) (fv t)
    λ-abstract = λ r -> foldr  lam                    r      rs
    saturate   = λ n -> foldl (λ r n' -> r · var n') (var n) rs

scε : ∀ {σ} -> ε ⊢ σ -> Result
scε = residualize [] ∘ proj₂ ∘ scatter [] ∘ map∞ (const (true , "")) ∘ build

-- tmap : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
-- tmap = ƛ fix ƛ ƛ caseList (var vz)
--                     nil
--                    (ƛ ƛ var (vs vs vs vs vz) · var (vs vz) :: var (vs vs vs vz) · var vz)

-- tmap-tmap : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
-- tmap-tmap = ƛ ƛ ƛ tmap · var (vs vs vz) · (tmap · var (vs vz) · var vz)

-- scε-tmap-tmap = scε (tmap-tmap {nat} {nat} {nat})
