module SC.Jigger where

open import SC.Basic

instance
  irefl : ∀ {α} {A : Set α} {x : A} -> x ≡ x
  irefl = refl

infixl 5 _<><_ _<>>_
infixr 6 _⇒ⁿ_
infix  9 _#_

Ren : Con -> Con -> Set
Ren Γ Δ = ∀ {σ} -> σ ∈ Γ -> σ ∈ Δ

_<><_ : Con -> Con -> Con
Γ <><  ε      = Γ
Γ <>< (Δ ▻ τ) = Γ ▻ τ <>< Δ

_<>>_ : Con -> Con -> Con
ε       <>> Δ = Δ
(Γ ▻ σ) <>> Δ = Γ <>> (Δ ▻ σ)

weak : ∀ {Γ} Δ -> Ren Γ (Γ <>< Δ)
weak  ε      v = v
weak (Δ ▻ σ) v = weak Δ (vs v)

fishy-chips : ∀ Γ Δ -> ε <>< (Δ <>> Γ) ≡ Δ <>< Γ
fishy-chips Γ  ε      = refl
fishy-chips Γ (Δ ▻ τ) = fishy-chips (Γ ▻ τ) Δ

lem : ∀ {Ξ Δ} Γ -> Δ <>> ε ≡ Γ <>> Ξ -> Γ <>< Ξ ≡ Δ
lem  ε      refl = fishy-chips ε _
lem (Γ ▻ σ) p    = lem Γ p

CoN : ℕ -> Set
CoN  0      = ⊤
CoN (suc n) = Type × CoN n

_⇒ⁿ_ : ∀ {n} -> CoN n -> Type -> Type
_⇒ⁿ_ {0}      _      τ = τ
_⇒ⁿ_ {suc n} (σ , Γ) τ = σ ⇒ Γ ⇒ⁿ τ

Bind : ∀ {n} -> Con -> CoN n -> Type -> Set
Bind {0}     Γ  _      σ = Γ ⊢ σ
Bind {suc n} Γ (τ , Δ) σ = (∀ {Δ Ξ} {{_ : Δ <>> ε ≡ Γ <>> (Ξ ▻ τ)}} -> Δ ⊢ τ) -> Bind (Γ ▻ τ) Δ σ

_#_ : ∀ n {Γ} {Δ : CoN n} {σ} -> Bind Γ Δ σ -> Γ ⊢ Δ ⇒ⁿ σ
_#_  0                  b = b
_#_ (suc n) {Γ} {τ , Δ} b = ƛ (n # b λ {Δ' Ξ} {{p}} -> subst (_⊢ τ) (lem Γ p) (var (weak Ξ vz)))
