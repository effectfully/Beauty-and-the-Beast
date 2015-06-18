module SC.Tests where

open import SC.Basic
open import SC.Main

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

titerate : ∀ {σ} -> Term ((σ ⇒ σ) ⇒ σ ⇒ list σ)
titerate = ƛ fix ƛ ƛ var vz :: var (vs vz) · (var (vs vs vz) · var vz)

-- titerate : ∀ {σ} -> Term ((σ ⇒ σ) ⇒ σ ⇒ list σ)
-- titerate = ƛ ƛ fix ƛ var (vs vz) :: tmap · var (vs vs vz) · var vz

succ : Term (nat ⇒ nat)
succ = ƛ s (var vz)

undefined : ∀ {σ} -> Term σ
undefined = fix ƛ var vz

tlookup : ∀ {σ} -> Term (nat ⇒ list σ ⇒ σ)
tlookup = fix ƛ ƛ ƛ caseList (var vz)
                       undefined
                      (ƛ ƛ caseNat (var (vs vs vs vz))
                             (var (vs vz))
                             (ƛ var (vs vs vs vs vs vz) · var vz · var (vs vz)))

tcontains-z : Term (list nat ⇒ nat)
tcontains-z = fix ƛ ƛ caseList (var vz)
                         z
                        (ƛ ƛ caseNat (var (vs vz))
                               (s z)
                               (ƛ var (vs vs vs vs vz) · var (vs vz)))

tcontains-z-tapp : Term (list nat ⇒ nat)
tcontains-z-tapp = ƛ tcontains-z · (tapp · var vz · (z :: nil))

tcontains-z-tapp-tapp : Term (list nat ⇒ list nat ⇒ nat)
tcontains-z-tapp-tapp = ƛ ƛ tcontains-z · (tapp · var (vs vz) · (tapp · (z :: nil) · var vz))

tzeros : Term (list nat)
tzeros = fix ƛ z :: var vz

tlookup-tzeros : Term (nat ⇒ nat)
tlookup-tzeros = ƛ tlookup · (var vz) · tzeros

teq : Term (nat ⇒ nat ⇒ nat)
teq = fix ƛ ƛ ƛ caseNat (var (vs vz))
                  (caseNat (var vz) (s z) (ƛ z))
                  (caseNat (var vz) (ƛ z) (ƛ ƛ var (vs vs vs vs vz) · var (vs vz) · var vz))

tω : Term nat
tω = fix ƛ s (var vz)

tcycle : ∀ {σ} -> Term (list σ ⇒ list σ)
tcycle = ƛ fix ƛ tapp · var (vs vz) · var vz

tλω : ∀ {σ} -> Term (σ ⇒ nat)
tλω = fix ƛ ƛ s (var (vs vz) · var vz)

tfoldr : ∀ {σ τ} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ list σ ⇒ τ)
tfoldr = ƛ ƛ fix ƛ ƛ caseList (var vz)
                       (var (vs vs vz))
                       (ƛ ƛ var (vs vs vs vs vs vz) · var (vs vz) · (var (vs vs vs vz) · var vz))

tmap' : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
tmap' = ƛ ƛ tfoldr · (ƛ ƛ var (vs vs vs vz) · var (vs vz) :: var vz) · nil · var vz

tmap'-tmap' : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
tmap'-tmap' = ƛ ƛ ƛ tmap' · var (vs vs vz) · (tmap' · var (vs vz) · var vz)

tfoldr-tapp : ∀ {σ τ} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ list σ ⇒ list σ ⇒ τ)
tfoldr-tapp = ƛ ƛ ƛ ƛ tfoldr · var (vs vs vs vz) · var (vs vs vz) · (tapp · var (vs vz) · var vz)

tdouble : Term (nat ⇒ nat)
tdouble = fix ƛ ƛ caseNat (var vz)
                    z
                   (ƛ s (s (var (vs vs vz) · var vz)))

teven : Term (nat ⇒ nat)
teven = fix ƛ ƛ caseNat (var vz)
                  (s z)
                  (ƛ caseNat (var vz)
                        z
                       (ƛ var (vs vs vs vz) · var vz))

teven-tdouble : Term (nat ⇒ nat)
teven-tdouble = ƛ teven · (tdouble · var vz)

tplus : Term (nat ⇒ nat ⇒ nat)
tplus = fix ƛ ƛ ƛ caseNat (var (vs vz))
                    (var vz)
                    (ƛ s (var (vs vs vs vz) · var vz · var (vs vz)))

tdouble-tplus : Term (nat ⇒ nat ⇒ nat)
tdouble-tplus = ƛ ƛ tdouble · (tplus · var (vs vz) · var vz)

tplus-tdouble : Term (nat ⇒ nat ⇒ nat)
tplus-tdouble = ƛ ƛ tplus · (tdouble · var (vs vz)) · (tdouble · var vz)

tmult : Term (nat ⇒ nat ⇒ nat)
tmult = fix ƛ ƛ ƛ caseNat (var (vs vz))
                     z
                    (ƛ tplus · var (vs vz) · (var (vs vs vs vz) · var vz · var (vs vz)))

tmult-tmult : Term (nat ⇒ nat ⇒ nat ⇒ nat)
tmult-tmult = ƛ ƛ ƛ tmult · (tmult · var (vs vs vz) · var (vs vz)) · var vz

tmap-titerate : ∀ {σ} -> Term ((σ ⇒ σ) ⇒ σ ⇒ list σ)
tmap-titerate = ƛ ƛ tmap · var (vs vz) · (titerate · var (vs vz) · var vz)

sands : Term (nat ⇒ nat)
sands = fix ƛ ƛ caseNat (var vz)
                  (var (vs vz) · var vz)
                  (ƛ s z)

tconcat : ∀ {σ} -> Term (list (list σ) ⇒ list σ)
tconcat = ƛ tfoldr · tapp · nil · var vz

tconcat-tmap-tconcat : ∀ {σ} -> Term (list (list (list σ)) ⇒ list σ)
tconcat-tmap-tconcat = ƛ tconcat · (tmap · tconcat · var vz)

id-nat : Term (nat ⇒ nat)
id-nat = fix ƛ ƛ caseNat (var vz)
                    z
                   (ƛ s (var (vs vs vz) · var vz))

id-nat-id-nat : Term (nat ⇒ nat)
id-nat-id-nat = ƛ id-nat · (id-nat · var vz)

caseNat-undefined : Term nat
caseNat-undefined = caseNat undefined z (ƛ z)

-- Seem ok.
scε-tmap-tmap             = λ {σ τ ν} -> scε (tmap-tmap {σ} {τ} {ν})
scε-tmap'-tmap'           = λ {σ τ ν} -> scε (tmap'-tmap' {σ} {τ} {ν})           
scε-tapp-tapp             = λ {σ}     -> scε (tapp-tapp {σ})
scε-tcontains-z-tapp      =              scε  tcontains-z-tapp
scε-tcontains-z-tapp-tapp =              scε  tcontains-z-tapp-tapp
scε-teq-tω-tω             =              scε (teq · tω · tω)
scε-s-tω                  =              scε (s tω) -- Needs folding.
scε-tλω-·                 = λ {σ}     -> scε (tλω {σ} · undefined)
scε-id-nat-id-nat         =              scε  id-nat-id-nat
scε-caseNat-undefined     =              scε  caseNat-undefined -- (case ⊥ of ...) ==> ⊥

-- Not sure.
scε-tfoldr-tapp           = λ {σ τ}   -> scε (tfoldr-tapp {σ} {τ})
scε-tdouble-tplus         =              scε  tdouble-tplus
scε-tplus-tdouble         =              scε  tplus-tdouble
scε-tcycle-cons           =              scε (z :: tcycle · (s z :: z :: nil))
scε-tlookup-tzeros        =              scε  tlookup-tzeros
scε-teven-tdouble         =              scε  teven-tdouble

-- sc-sands-·                =              sc {ε ▻ nat} (sands · var vz)

-- Do not terminate.
scε-tmap-titerate         = λ {σ}     -> scε (tmap-titerate {σ})
scε-tconcat-tmap-tconcat  = λ {σ}     -> scε (tconcat-tmap-tconcat {σ})

open import SC.NbE
