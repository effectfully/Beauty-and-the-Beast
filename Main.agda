module SC.Main where

open import Function
open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.List.Base
open import Coinduction

open import SC.Basic
open import SC.NbE

weakenʷ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ʷ σ
weakenʷ ψ = weaken ψ ∘ toʷ

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

History = List Syntax

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
  go h x = maybe (go (erase nx ∷ h)) nx (unroll h nx) where nx = norm x

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
