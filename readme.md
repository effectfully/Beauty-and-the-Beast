# Overview

It's a toy supercompiler for STLC with numbers, lists, pattern matching and general recursion.

## Baby steps.

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

`sc tmap-tmap` gives

```
lam "x0"
(lam "x1"
 (lam "x2"
  (Let "h3" :=
   lam "x0"
   (lam "x1"
    (lam "x2"
     (caseList (var "x2") nil
      (lam "x4"
       (lam "x5"
        (var "x0" · (var "x1" · var "x4") ::
         var "h3" · var "x0" · var "x1" · var "x5"))))))
   In (var "h3" · var "x0" · var "x1" · var "x2"))))
```

which looks OK modulo η-expansion.

`sc tapp-tapp` gives

```
lam "x0"
(lam "x1"
 (lam "x2"
  (Let "h3" :=
   lam "x0"
   (lam "x1"
    (lam "x2"
     (caseList (var "x0")
      (caseList (var "x1") (var "x2")
       (lam "x4"
        (lam "x5"
         (var "x4" ::
          (Let "h6" :=
           lam "x5"
           (lam "x2"
            (caseList (var "x5") (var "x2")
             (lam "x7"
              (lam "x8" (var "x7" :: var "h6" · var "x8" · var "x2")))))
           In (var "h6" · var "x5" · var "x2"))))))
      (lam "x4"
       (lam "x5"
        (var "x4" :: var "h3" · var "x5" · var "x1" · var "x2"))))))
   In (var "h3" · var "x0" · var "x1" · var "x2"))))
```

which looks OK modulo η-expansion and unnecessary unfolding of the `h6` function.