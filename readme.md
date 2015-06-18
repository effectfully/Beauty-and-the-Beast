# Overview

It's a toy supercompiler for STLC with numbers, lists, pattern matching and general recursion.

## Baby steps

```
tmap : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
tmap = ƛ fix ƛ ƛ caseList (var vz)
                    nil
                   (ƛ ƛ var (vs vs vs vs vz) · var (vs vz) :: var (vs vs vs vz) · var vz)

tmap-tmap : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
tmap-tmap = ƛ ƛ ƛ tmap · var (vs vs vz) · (tmap · var (vs vz) · var vz)

tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ)
tapp = fix ƛ ƛ ƛ caseList (var (vs vz))
                   (var vz)
                   (ƛ ƛ var (vs vz) :: var (vs vs vs vs vz) · var vz · var (vs vs vz))

tapp-tapp : ∀ {σ} -> Term (list σ ⇒ list σ ⇒ list σ ⇒ list σ)
tapp-tapp = ƛ ƛ ƛ tapp · (tapp · var (vs vs vz) · var (vs vz)) · var vz
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
tdouble = fix ƛ ƛ caseNat (var vz)
                    z
                   (ƛ s (s (var (vs vs vz) · var vz)))

tplus : Term (nat ⇒ nat ⇒ nat)
tplus = fix ƛ ƛ ƛ caseNat (var (vs vz))
                    (var vz)
                    (ƛ s (var (vs vs vs vz) · var vz · var (vs vz)))

tdouble-tplus : Term (nat ⇒ nat ⇒ nat)
tdouble-tplus = ƛ ƛ tdouble · (tplus · var (vs vz) · var vz)

tplus-tdouble : Term (nat ⇒ nat ⇒ nat)
tplus-tdouble = ƛ ƛ tplus · (tdouble · var (vs vz)) · (tdouble · var vz)
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