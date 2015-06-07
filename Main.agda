module SC.Main where

open import Function
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.List.Base as List
open import Data.Vec
open import Coinduction

open import SC.Basic
open import SC.NbE

data Perforate Γ σ : Set where
  before : Perforate Γ σ
  now    : ∀ {τ} -> Γ ⊢ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ τ -> Δ ⊢ʷ σ) -> Perforate Γ σ

compᵖ : ∀ {Γ σ τ}
      -> Perforate Γ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ σ -> Δ ⊢ʷ τ) -> Perforate Γ σ -> Perforate Γ τ
compᵖ p d  before   = p
compᵖ p d (now a c) = now a (λ ψ x -> d ψ (c ψ x))

mapᵖ : ∀ {Γ σ τ}
     -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ σ -> Δ ⊢ʷ τ) -> Perforate Γ σ -> Perforate Γ τ
mapᵖ = compᵖ before

-- We never use `weaken': only `weakenʷ'. So it's pointless.
-- Do we need to apply `toʷ' before perforating? Or even before building?
perforate : ∀ {Γ σ} -> Γ ⊢ σ -> Perforate Γ σ
perforate (var v)           = before
perforate (ƛ b)             = before
perforate (f · x)           = compᵖ (mapᵖ (λ ψ x'  -> weakenʷ ψ f · x')   (perforate x))
                                    (λ ψ f'  -> f' · weakenʷ ψ x)
                                    (perforate f)
perforate (fix f)           = before
perforate  z                = before
perforate (s n)             = mapᵖ (λ ψ n' -> s n') (perforate n)
perforate (caseNat  n  y g) = compᵖ (now n  f) f (perforate n) where
  f = λ {Δ} (ψ : _ ⊆ Δ) n'  -> caseNat  n'  (weakenʷ ψ y) (weakenʷ ψ g)
perforate  nil              = before
perforate (x :: xs)         = compᵖ (mapᵖ (λ ψ xs' -> weakenʷ ψ x :: xs') (perforate xs))
                                    (λ ψ x'  -> x' :: weakenʷ ψ xs)
                                    (perforate x)
perforate (caseList xs y g) = compᵖ (now xs f) f (perforate xs) where
  f = λ {Δ} (ψ : _ ⊆ Δ) xs' -> caseList xs' (weakenʷ ψ y) (weakenʷ ψ g)

History = List Spine

unroll : ∀ {Γ σ} -> History -> Γ ⊢ σ -> Maybe (Γ ⊢ σ)
unroll h (f · x) = (_· x) <$> unroll h f
unroll h (fix f) = just (f · (fix f))
unroll h (caseNat  n  y g) = (λ n'  -> caseNat  n'  y g) <$> unroll h n
unroll h (caseList xs y g) = (λ xs' -> caseList xs' y g) <$> unroll h xs
unroll h  x = nothing

{-# NON_TERMINATING #-} -- Due to the absense of a termination criteria.
reduce : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
reduce = go [] where
  go : _ -> _ -> _
  go h x = maybe (go (spine nx ∷ h)) nx (unroll h nx) where nx = norm x

revert : ∀ {Γ σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ σ -> Δ ⊢ʷ τ) -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
revert d x with mapᵖ d (perforate (reduce x))
... | before      = nothing
... | now {τ} a c with λ {Δ} (ψ : _ ⊆ Δ) x -> norm (unʷ (c ψ x))
... | finish with τ
... | nat    = just (caseNat   a
                              (   finish  stop        z            )
                              (ƛ (finish (skip stop) (s (var vz)))))
... | list _ = just (caseList  a
                              (     finish  stop               nil                     )
                              (ƛ ƛ (finish (skip (skip stop)) (var (vs vz) :: var vz))))
... | _      = ⊥ where postulate ⊥ : _ -- It shouldn't be hard to remove this.

{-# TERMINATING #-} -- What am I doing wrong?
build : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢∞ σ
build (ƛ b) = ƛ (build b)
build (s n)             = s (build n)
build (caseNat  n  y g) =
  maybe  build
        (caseNat  n  (build y) (build g))
        (revert (λ ψ n'  -> caseNat  n'  (weakenʷ ψ y) (weakenʷ ψ g)) n)
build (x :: xs)         = build x :: build xs
build (caseList xs y g) =
  maybe  build
        (caseList xs (build y) (build g))
        (revert (λ ψ xs' -> caseList xs' (weakenʷ ψ y) (weakenʷ ψ g)) xs)
build x = maybe (λ x' -> keep x (♯ build x')) (stop x) (revert (λ ψ x' -> x') x)

toResult : ∀ {Γ σ} -> ℕ -> Vec Name (lengthᶜᵒⁿ Γ) -> Γ ⊢ σ -> Result
toResult new ρ (var v) = var (lookup (∈-to-Fin v) ρ)
toResult new ρ (ƛ b)   = lam xn (toResult (suc new) (xn ∷ ρ) b) where xn = "x" ++ℕ new
toResult new ρ (f · x) = toResult new ρ f · toResult new ρ x
toResult new ρ (fix f) = ⊥ where postulate ⊥ : _ -- Fix this.
toResult new ρ  z                = z
toResult new ρ (s n)             = s (toResult new ρ n)
toResult new ρ (caseNat  n  y g) = caseNat  (toResult new ρ n)  (toResult new ρ y) (toResult new ρ g)
toResult new ρ  nil              = nil
toResult new ρ (x :: xs)         = toResult new ρ x :: toResult new ρ xs
toResult new ρ (caseList xs y g) = caseList (toResult new ρ xs) (toResult new ρ y) (toResult new ρ g)

{-# NON_TERMINATING #-} -- Due to the absense of a termination criteria.
residualize : ∀ {Γ σ}
            -> ℕ -> List (Spine × Name) -> Vec Name (lengthᶜᵒⁿ Γ) -> Γ ⊢∞ σ -> Result
residualize new Ξ ρ (ƛ b) = lam xn (residualize (suc new) Ξ (xn ∷ ρ) b) where xn = "x" ++ℕ new
residualize new Ξ ρ (s n)             = s (residualize new Ξ ρ n)
residualize new Ξ ρ (caseNat  n  y g) =
  caseNat  (toResult new ρ n)  (residualize new Ξ ρ y) (residualize new Ξ ρ g)
residualize new Ξ ρ (x :: xs)         = residualize new Ξ ρ x :: residualize new Ξ ρ xs
residualize new Ξ ρ (caseList xs y g) =
  caseList (toResult new ρ xs) (residualize new Ξ ρ y) (residualize new Ξ ρ g)
residualize new Ξ ρ (stop x)   = toResult new ρ x
residualize new Ξ ρ (keep t x) =
  maybe  saturate
        (Let hn := λ-abstract (residualize (suc new) ((et , hn) ∷ Ξ) ρ (♭ x)) In saturate hn)
        (lookup-for et Ξ)
  where
    et = spine t
    hn = "h" ++ℕ new
    rs = List.map (flip lookup ρ) (fv stop t)
    λ-abstract = λ r -> List.foldr  lam                    r      rs
    saturate   = λ n -> List.foldl (λ r n' -> r · var n') (var n) rs

-- Add identity environment.
sc : ∀ {σ} -> ε ⊢ σ -> Result
sc = residualize 0 [] [] ∘ build ∘ norm
