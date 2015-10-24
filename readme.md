# Overview

It's a toy supercompiler for STLC with numbers, lists, pattern matching and general recursion.

## Data

We have

Terms (after expanding of aliases):

```
data _⊢_ (Γ : Con) : Type -> Set where
  var  : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ
  fix_ : ∀ {σ}   -> Γ ⊢ σ ⇒ σ -> Γ ⊢ σ
  z        :            Γ ⊢ nat
  s        :            Γ ⊢ nat    -> Γ ⊢ nat
  caseNat  : ∀ {σ}   -> Γ ⊢ nat    -> Γ ⊢ σ      -> Γ ⊢ nat ⇒ σ        -> Γ ⊢ σ
  nil      : ∀ {σ}   -> Γ ⊢ list σ
  _::_     : ∀ {σ}   -> Γ ⊢ σ      -> Γ ⊢ list σ -> Γ ⊢ list σ
  caseList : ∀ {σ τ} -> Γ ⊢ list σ -> Γ ⊢ τ      -> Γ ⊢ σ ⇒ list σ ⇒ τ -> Γ ⊢ τ
```

Some [nice syntactic sugar](https://github.com/effectfully/Beauty-and-the-Beast/blob/master/Jigger.agda) stolen from Conor McBride and generalized to handle n-ary lambdas.

Two NbEs ([type-directed](https://github.com/effectfully/Beauty-and-the-Beast/blob/master/TDNbE.agda), [non-strictly positive](https://github.com/effectfully/Beauty-and-the-Beast/blob/master/NbE.agda)).

Infinite lambda terms (after expanding of aliases):

```
data _⊢∞_  : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ      -> Γ ⊢∞ σ
  ƛ_  : ∀ {σ τ} -> Γ ▻ σ ⊢∞ τ -> Γ ⊢∞ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢∞ σ ⇒ τ -> Γ ⊢∞ σ     -> Γ ⊢∞ τ
  z        :            Γ ⊢∞ nat
  s        :            Γ ⊢∞ nat    -> Γ ⊢∞ nat
  caseNat  : ∀ {σ}   -> Γ ⊢∞ nat    -> Γ ⊢∞ σ      -> Γ ⊢∞ nat ⇒ σ        -> Γ ⊢∞ σ
  nil      : ∀ {σ}   -> Γ ⊢∞ list σ
  _::_     : ∀ {σ}   -> Γ ⊢∞ σ      -> Γ ⊢∞ list σ -> Γ ⊢∞ list σ
  caseList : ∀ {σ τ} -> Γ ⊢∞ list σ -> Γ ⊢∞ τ      -> Γ ⊢∞ σ ⇒ list σ ⇒ τ -> Γ ⊢∞ τ
  checkpoint : ∀ {σ} -> Tag -> Γ ⊢ σ -> ∞ (Γ ⊢∞ σ) -> Γ ⊢∞ σ
```

Every infinite lambda term represents unfolding of a regular lambda term (note the absense of `fix_`). Recursion happens in the `checkpoint` constructor, which also receives some configuration.

And the destination:

```
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
```

## Supercompilation

**THE CODE WAS CHANGED**. But it became more obfuscated, and the algorithm remains almost entirely the same, so I'll leave this section untouched.

The `revert` function

```
revert : ∀ {Γ σ τ} -> (∀ {Δ} -> Γ ⊆ Δ -> Δ ⊢ σ -> Δ ⊢ τ) -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
```

transforms an expression as follows (abusing the notation):

    revert cont (case (case x of c -> e) of c' -> e')

==>

    case x of c -> cont _ (case e of c' -> e').

I.e. it picks the inner `case` (for any number of nested `case`s), makes it outer and applies a continuation to the remaining expression.

`unroll` unfolds one `fix` like this:

```
unroll : ∀ {Γ σ} -> Γ ⊢ σ -> Maybe (Γ ⊢ σ)
unroll (f · x) = (_· x) <$> unroll f
unroll (fix f) = just (f · (fix f))
unroll (caseNat  n  y g) = (λ n'  -> caseNat  n'  y g) <$> unroll n
unroll (caseList xs y g) = (λ xs' -> caseList xs' y g) <$> unroll xs
unroll  x = nothing
```

Supercompilation stuff happens in the `build` function:

```
mutual
  build-go : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢∞ σ
  build-go (var v) = var v
  build-go (ƛ b)   = ƛ (build b)
  build-go (f · x) = build f · build x
  build-go (fix f) = ⊥ where postulate ⊥ : _
  build-go  z                = z
  build-go (s n)             = s (build n)
  build-go (caseNat  n  y g) =
    maybe′  build
           (check (caseNat  n  y g) (♯ caseNat  (build n)  (build y) (build g)))
           (revert (λ ψ n'  -> caseNat  n'  (weaken ψ y) (weaken ψ g)) n)
  build-go  nil              = nil
  build-go (x :: xs)         = build x :: build xs
  build-go (caseList xs y g) =
    maybe′  build
           (check (caseList xs y g) (♯ caseList (build xs) (build y) (build g)))
           (revert (λ ψ xs' -> caseList xs' (weaken ψ y) (weaken ψ g)) xs)

  build : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢∞ σ
  build x =
    maybe (λ x' -> check x (♯ build (norm x')))
          (build-go x)
          (unroll x)
```

In the `caseNat` and `caseList` cases we essentially perform this transformation:

    case (case (case x of c -> e) of c' -> e') of c'' -> e''

==>

    case x of c -> case (case e of c' -> e') of c'' -> e''

and then call `build` recursively. When there are no nested `case`s, we make a checkpoint (this is not necessary, but results in more compact resulting code; if we would make checkpoints in the `s n` case too, then we could fold `succ · fix succ` into `fix succ` for example) and `build` all subexpressions.

In the `build` function we make a checkpoint every time `unroll` succeeds.

## Residualization

The `scatter` function deletes all checkpoints, that do not correspond to calls to recursive functions:

```
scatter : ∀ {n Γ σ} -> Vec (Spine × Name) n -> Γ ⊢∞ σ -> List Name × Γ ⊢∞ σ
```

The `residualize` function transforms an infinite lambda term into a finite `Result`.

```
residualize : ∀ {Γ σ} -> Vec Name (lengthᶜᵒⁿ Γ) -> Γ ⊢∞ σ -> Result
```

Finally, `scε` is

```
scε : ∀ {σ} -> ε ⊢ σ -> Result
scε = residualize [] ∘ proj₂ ∘ scatter [] ∘ build ∘ norm
```

## Examples

```
tmap : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
tmap = 1 # λ f → fix 2 # λ r xs → caseList xs
                            nil
                           (2 # λ x xs' → f · x :: r · xs')

tmap-tmap : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
tmap-tmap = 3 # λ g f xs → tmap · g · (tmap · f · xs)

tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ)
tapp = fix 3 # λ r xs ys → caseList xs
                  ys
                 (2 # λ x xs' → x :: r · xs' · ys)

tapp-tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ ⇒ list σ)
tapp-tapp = 3 # λ xs ys zs → tapp · (tapp · xs · ys) · zs
```

`scε tmap-tmap` gives

```
lam "x0"
(lam "x1"
 (lam "x2"
  (Let "r0" :=
   lam "x0"
   (lam "x1"
    (lam "x2"
     (caseList (var "x2") nil
      (lam "x3"
       (lam "x4"
        (var "x0" · (var "x1" · var "x3") ::
         var "r0" · var "x0" · var "x1" · var "x4"))))))
   In (var "r0" · var "x0" · var "x1" · var "x2"))))
```

which looks OK modulo η-expansion.

`scε tapp-tapp` gives

```
lam "x0"
(lam "x1"
 (lam "x2"
  (Let "r0" :=
   lam "x0"
   (lam "x1"
    (lam "x2"
     (caseList (var "x0")
      (Let "r3" :=
       lam "x1"
       (lam "x2"
        (caseList (var "x1") (var "x2")
         (lam "x3"
          (lam "x4" (var "x3" :: var "r3" · var "x4" · var "x2")))))
       In (var "r3" · var "x1" · var "x2"))
      (lam "x3"
       (lam "x4"
        (var "x3" :: var "r0" · var "x4" · var "x1" · var "x2"))))))
   In (var "r0" · var "x0" · var "x1" · var "x2"))))
```

which looks OK modulo η-expansion.

```
tdouble : Term (nat ⇒ nat)
tdouble = fix 2 # λ r n → caseNat n
                     z
                    (1 # λ n' → s (s (r · n')))

tplus : Term (nat ⇒ nat ⇒ nat)
tplus = fix 3 # λ r n m → caseNat n
                   m
                  (1 # λ n' → s (r · n' · m))

tdouble-tplus : Term (nat ⇒ nat ⇒ nat)
tdouble-tplus = 2 # λ n m → tdouble · (tplus · n · m)

tplus-tdouble : Term (nat ⇒ nat ⇒ nat)
tplus-tdouble = 2 # λ n m → tplus · (tdouble · n) · (tdouble · m)
```

Both `tdouble-tplus` and `tplus-tdouble` supercompile to the same expression:

```
lam "x0"
(lam "x1"
 (Let "r0" :=
  lam "x0"
  (lam "x1"
   (caseNat (var "x0")
    (Let "r3" :=
     lam "x1"
     (caseNat (var "x1") z (lam "x2" (s (s (var "r3" · var "x2")))))
     In (var "r3" · var "x1"))
    (lam "x2" (s (s (var "r0" · var "x2" · var "x1"))))))
  In (var "r0" · var "x0" · var "x1")))
```