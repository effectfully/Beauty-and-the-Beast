module SC.Main where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.List.Base hiding (unfold)

open import SC.Basic
open import SC.NbE

unfold : ∀ {Γ σ} -> Γ ⊢ σ -> Maybe (Γ ⊢ σ)
unfold (ƛ b)   = ƛ_ <$> unfold b
unfold (f · x) = (_· x) <$> unfold f
unfold (fix f) = just (f · (fix f))
unfold (caseNat  n  y g) = (λ n'  -> caseNat  n'  y g) <$> unfold n
unfold (caseList xs y g) = (λ xs' -> caseList xs' y g) <$> unfold xs
unfold _ = nothing

{-# NON_TERMINATING #-}
reduce : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
reduce x = maybe reduce nx (unfold nx) where nx = norm x

weakenʷ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ʷ σ
weakenʷ ψ = weaken ψ ∘ toʷ

data Perforate Γ σ : Set where
  before : Perforate Γ σ
  now    : ∀ {τ} -> Γ ⊢ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ τ -> Δ ⊢ʷ σ) -> Perforate Γ σ

compᵖ : ∀ {Γ σ τ}
      -> Perforate Γ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ σ -> Δ ⊢ʷ τ) -> Perforate Γ σ -> Perforate Γ τ
compᵖ p f  before   = p
compᵖ p f (now a c) = now a (λ ψ x -> f ψ (c ψ x))

mapᵖ : ∀ {Γ σ τ}
     -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ʷ σ -> Δ ⊢ʷ τ) -> Perforate Γ σ -> Perforate Γ τ
mapᵖ = compᵖ before

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

{-# NON_TERMINATING #-}
mutual
  optimize : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
  optimize x with reduce x
  ... | rx with perforate rx
  ... | before      = rx
  ... | now {τ} a c with τ
  ... | nat    = caseNat   a
                          (continue (c stop z))
                          (continue (ƛ c         (skip stop)  (s (var vz))))
  ... | list _ = caseList  a
                          (continue (c stop nil))
                          (continue (ƛ ƛ c (skip (skip stop)) (var (vs vz) :: var vz)))
  ... | _      = ⊥ where postulate ⊥ : _ -- It shouldn't be hard to remove this.

  -- Every `continue' peels off one case-expression, so NON_TERMINATING is only due to
  -- the absense of a termination criteria in `reduce'.
  continue : ∀ {Γ σ} -> Γ ⊢ʷ σ -> Γ ⊢ σ
  continue = optimize ∘ unʷ stop

{-# NON_TERMINATING #-}
mutual
  traverse : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
  traverse (ƛ b)   = ƛ (sc b)
  traverse (caseNat  n  y g) = caseNat  n  (sc y) (sc g)
  traverse (caseList xs y g) = caseList xs (sc y) (sc g)
  traverse  x = x

  sc : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
  sc = traverse ∘ optimize



tmap : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
tmap = ƛ fix ƛ ƛ caseList (var vz)
                    nil
                   (ƛ ƛ var (vs vs vs vs vz) · var (vs vz) :: var (vs vs vs vz) · var vz)

tmap-tmap : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
tmap-tmap = ƛ ƛ ƛ tmap · var (vs vs vz) · (tmap · var (vs vz) · var vz)
