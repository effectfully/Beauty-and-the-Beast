module SC.Main where

open import Function
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe.Base
open import Data.Product
open import Data.List.Base as List
open import Data.Vec as Vec hiding (_⊛_)
open import Coinduction

open import SC.Basic
open import SC.NbE

data Perforate Γ σ : Set where
  before : Perforate Γ σ
  now    : ∀ {τ} -> Γ ⊢ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ τ -> Δ ⊢ σ) -> Perforate Γ σ

compᵖ : ∀ {Γ σ τ}
      -> Perforate Γ τ -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ σ -> Δ ⊢ τ) -> Perforate Γ σ -> Perforate Γ τ
compᵖ p d  before   = p
compᵖ p d (now a c) = now a (λ ψ x -> d ψ (c ψ x))

mapᵖ : ∀ {Γ σ τ}
     -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ σ -> Δ ⊢ τ) -> Perforate Γ σ -> Perforate Γ τ
mapᵖ = compᵖ before

perforate : ∀ {Γ σ} -> Γ ⊢ σ -> Perforate Γ σ
perforate (var v)           = before
perforate (ƛ b)             = before
perforate (f · x)           = compᵖ (mapᵖ (λ ψ x'  -> weaken ψ f · x')   (perforate x))
                                    (λ ψ f'  -> f' · weaken ψ x)
                                    (perforate f)
perforate (fix f)           = before
perforate  z                = before
perforate (s n)             = mapᵖ (λ ψ n' -> s n') (perforate n)
perforate (caseNat  n  y g) = compᵖ (now n  f) f (perforate n) where
  f = λ {Δ} (ψ : _ ⊆ Δ) n'  -> caseNat  n'  (weaken ψ y) (weaken ψ g)
perforate  nil              = before
perforate (x :: xs)         = compᵖ (mapᵖ (λ ψ xs' -> weaken ψ x :: xs') (perforate xs))
                                    (λ ψ x'  -> x' :: weaken ψ xs)
                                    (perforate x)
perforate (caseList xs y g) = compᵖ (now xs f) f (perforate xs) where
  f = λ {Δ} (ψ : _ ⊆ Δ) xs' -> caseList xs' (weaken ψ y) (weaken ψ g)

revert : ∀ {Γ σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ σ -> Δ ⊢ τ) -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
revert d x with mapᵖ d (perforate x)
... | before      = nothing
... | now {τ} a c with λ {Δ} (ψ : _ ⊆ Δ) x -> norm (c ψ x)
... | finish with τ
... | nat    = just (caseNat   a
                              (   finish  stop        z            )
                              (ƛ (finish (skip stop) (s (var vz)))))
... | list _ = just (caseList  a
                              (     finish  stop               nil                     )
                              (ƛ ƛ (finish (skip (skip stop)) (var (vs vz) :: var vz))))
... | _      = ⊥ where postulate ⊥ : _ -- It should be easy to remove this.

unroll : ∀ {Γ σ} -> Γ ⊢ σ -> Maybe (Γ ⊢ σ)
unroll (f · x) = (_· x) <$> unroll f
unroll (fix f) = just (f · (fix f))
unroll (caseNat  n  y g) = (λ n'  -> caseNat  n'  y g) <$> unroll n
unroll (caseList xs y g) = (λ xs' -> caseList xs' y g) <$> unroll xs
unroll  x = nothing

check : ∀ {Γ σ} -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ 
check = checkpoint true ""

{-# TERMINATING #-}
mutual
  build-go : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢∞ σ
  build-go (var v) = var v
  build-go (ƛ b)   = ƛ (build b)
  build-go (f · x) = build f · build x
  build-go (fix f) = ⊥ where postulate ⊥ : _ -- build (norm (f · (fix f)))
  build-go  z                = z
  build-go (s n)             = s (build n) -- check (s n) (♯ s (build n))
  build-go (caseNat  n  y g) =
    maybe′  build
           (check (caseNat  n  y g) (♯ caseNat  (build n)  (build y) (build g)))
           -- (caseNat  (build n)  (build y) (build g))
           (revert (λ ψ n'  -> caseNat  n'  (weaken ψ y) (weaken ψ g)) n)
  build-go  nil              = nil
  build-go (x :: xs)         = build x :: build xs -- check (x :: xs) (♯ (build x :: build xs))
  build-go (caseList xs y g) =
    maybe′  build
           (check (caseList xs y g) (♯ caseList (build xs) (build y) (build g)))
           -- (caseList (build xs) (build y) (build g))
           (revert (λ ψ xs' -> caseList xs' (weaken ψ y) (weaken ψ g)) xs)

  build : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢∞ σ
  build x =
    maybe (λ x' -> check x (♯ build (norm x')))
          (build-go x)
          (unroll x)

{-# NON_TERMINATING #-} -- Due to the absense of a termination criteria.
scatter : ∀ {n Γ σ} -> Vec (Spine × Name) n -> Γ ⊢∞ σ -> List Name × Γ ⊢∞ σ 
scatter       ρ (var v) = return (var v)
scatter       ρ (ƛ b)   = ƛ_ <$> scatter ρ b
scatter       ρ (f · x) = _·_ <$> scatter ρ f ⊛ scatter ρ x
scatter       ρ  z                = return z
scatter       ρ (s n)             = s <$> scatter ρ n
scatter       ρ (caseNat  n  y g) = caseNat  <$> scatter ρ n  ⊛ scatter ρ y ⊛ scatter ρ g
scatter       ρ  nil              = return nil
scatter       ρ (x :: xs)         = _::_ <$> scatter ρ x ⊛ scatter ρ xs
scatter       ρ (caseList xs y g) = caseList <$> scatter ρ xs ⊛ scatter ρ y ⊛ scatter ρ g
scatter {new} ρ (checkpoint _ _ t x) =
  maybe (λ rn' -> rn' ∷ [] , checkpoint true rn' t x)
        (case scatter ((et , rn) ∷ ρ) (♭ x) of λ{
            (ns , x') -> maybe (λ ns' -> ns' , checkpoint false rn t (♯ x'))
                               (ns , x')
                               (deletem rn ns)
        })
        (lookup-for et (Vec.toList ρ))
  where
    et = spine t
    rn = "r" ++ℕ new

len : ∀ {n α} {A : Set α} -> Vec A n -> ℕ
len {n} _ = n

{-# NON_TERMINATING #-} -- Because `scatter' is non-terminating.
residualize : ∀ {Γ σ} -> Vec Name (lengthᶜᵒⁿ Γ) -> Γ ⊢∞ σ -> Result
residualize ρ (var v) = var (lookup (∈-to-Fin v) ρ)
residualize ρ (ƛ b)   = lam xn (residualize (xn ∷ ρ) b) where xn = "x" ++ℕ len ρ
residualize ρ (f · x) = residualize ρ f · residualize ρ x
residualize ρ  z                = z
residualize ρ (s n)             = s (residualize ρ n)
residualize ρ (caseNat  n  y g) =
  caseNat  (residualize ρ n)  (residualize ρ y) (residualize ρ g)
residualize ρ  nil              = nil
residualize ρ (x :: xs)         = residualize ρ x :: residualize ρ xs
residualize ρ (caseList xs y g) =
  caseList (residualize ρ xs) (residualize ρ y) (residualize ρ g)
residualize ρ (checkpoint seen rn t x) =
  if seen then saturate rn else (Let rn := λ-abstract (residualize ρ (♭ x)) In saturate rn)
  where
    rs = List.map (flip lookup ρ) (nub (fv-all stop t))
    λ-abstract = λ r -> List.foldr  lam                    r      rs
    saturate   = λ n -> List.foldl (λ r n' -> r · var n') (var n) rs

scε : ∀ {σ} -> ε ⊢ σ -> Result
scε = residualize [] ∘ proj₂ ∘ scatter [] ∘ build ∘ norm

-- supply : ℕ -> ∀ Γ -> Vec Name (lengthᶜᵒⁿ Γ)
-- supply new  ε      = []
-- supply new (Γ ▻ σ) = ("x" ++ℕ new) ∷ supply (suc new) Γ

-- sc : ∀ {Γ σ} -> Γ ⊢ σ -> Result
-- sc {Γ} = residualize (supply 0 Γ) ∘ proj₂ ∘ scatter [] ∘ build ∘ norm

-- tmap : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
-- tmap = ƛ fix ƛ ƛ caseList (var vz)
--                     nil
--                    (ƛ ƛ var (vs vs vs vs vz) · var (vs vz) :: var (vs vs vs vz) · var vz)

-- tmap-tmap : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
-- tmap-tmap = ƛ ƛ ƛ tmap · var (vs vs vz) · (tmap · var (vs vz) · var vz)

-- tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ)
-- tapp = fix ƛ ƛ ƛ caseList (var (vs vz))
--                    (var vz)
--                    (ƛ ƛ var (vs vz) :: var (vs vs vs vs vz) · var vz · var (vs vs vz))

-- tapp-tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ ⇒ list σ)
-- tapp-tapp = ƛ ƛ ƛ tapp · (tapp · var (vs vs vz) · var (vs vz)) · var vz
