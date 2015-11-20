module SC.Tests where

open import SC.Basic
open import SC.Jigger
open import SC.SC

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

-- Should this be a constructor instead?
undefined : ∀ {σ} -> Term σ
undefined = fix 1 # λ x → x

titerate : ∀ {σ} -> Term ((σ ⇒ σ) ⇒ σ ⇒ list σ)
titerate = 1 # λ f → fix 2 # λ r x -> x :: r · (f · x)

tlookup : ∀ {σ} -> Term (nat ⇒ list σ ⇒ σ)
tlookup = fix 3 # λ r n xs → caseList xs
                     undefined
                    (2 # λ x xs' → caseNat n
                            x
                           (1 # λ n' → r · n' · xs'))
module _ where                           
-- abstract
  bool = nat

  tfalse : Term bool
  tfalse = z

  ttrue : Term bool
  ttrue = s z

  tif : ∀ {σ} -> Term (bool ⇒ σ ⇒ σ ⇒ σ)
  tif = 3 # λ b x y → caseNat b x (1 # λ _ → y)

test-bool : Term (bool ⇒ nat)
test-bool = 1 # λ b → tif · b · z · s z

tcontains-z : Term (list nat ⇒ bool)
tcontains-z = fix 2 # λ r ns → caseList ns
                         tfalse
                        (2 # λ n ns' → caseNat n
                                ttrue
                               (1 # λ _ → r · ns'))

tcontains-z-tapp : Term (list nat ⇒ bool)
tcontains-z-tapp = 1 # λ ns → tcontains-z · (tapp · ns · (z :: nil))

tcontains-z-tapp-tapp : Term (list nat ⇒ list nat ⇒ bool)
tcontains-z-tapp-tapp = 2 # λ ns ms → tcontains-z · (tapp · ns · (tapp · (z :: nil) · ms))

tzeros : Term (list nat)
tzeros = fix 1 # λ ns → z :: ns

tlookup-tzeros : Term (nat ⇒ nat)
tlookup-tzeros = 1 # λ n → tlookup · n · tzeros

teq : Term (nat ⇒ nat ⇒ bool)
teq = fix 3 # λ r n m → caseNat n
                (caseNat m  ttrue             (1 # λ _ → tfalse))
                (caseNat m (1 # λ _ → tfalse) (2 # λ n' m' → r · n' · m'))

tω : Term nat
tω = fix 1 # λ ω → s ω

tcycle : ∀ {σ} -> Term (list σ ⇒ list σ)
tcycle = 1 # λ xs → fix (tapp · xs)

tλω : ∀ {σ} -> Term (σ ⇒ nat)
tλω = fix 2 # λ r n → s (r · n)

tfoldr : ∀ {σ τ} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ list σ ⇒ τ)
tfoldr = 2 # λ f z → fix 2 # λ r xs → caseList xs
                                z
                               (2 # λ x xs' → f · x · (r · xs'))

tmap' : ∀ {σ τ} -> Term ((σ ⇒ τ) ⇒ list σ ⇒ list τ)
tmap' = 1 # λ f → tfoldr · (2 # λ x rs → f · x :: rs) · nil

tmap'-tmap' : ∀ {σ τ ν} -> Term ((τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ list σ ⇒ list ν)
tmap'-tmap' = 3 # λ g f xs → tmap' · g · (tmap' · f · xs)

tfoldr-tapp : ∀ {σ τ} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ list σ ⇒ list σ ⇒ τ)
tfoldr-tapp = 4 # λ f z xs ys → tfoldr · f · z · (tapp · xs · ys)

tfoldr-tfoldr : ∀ {σ τ} -> Term ((σ ⇒ τ ⇒ τ) ⇒ τ ⇒ list σ ⇒ list σ ⇒ τ)
tfoldr-tfoldr = 4 # λ f z xs ys → tfoldr · f · (tfoldr · f · z · ys) · xs

tdouble : Term (nat ⇒ nat)
tdouble = fix 2 # λ r n → caseNat n
                     z
                    (1 # λ n' → s (s (r · n')))

teven : Term (nat ⇒ bool)
teven = fix 2 # λ r n → caseNat n
                   ttrue
                  (1 # λ n' → caseNat n'
                          tfalse
                         (1 # λ n'' → r · n''))

teven-tdouble : Term (nat ⇒ bool)
teven-tdouble = 1 # λ n → teven · (tdouble · n)

tplus : Term (nat ⇒ nat ⇒ nat)
tplus = fix 3 # λ r n m → caseNat n
                   m
                  (1 # λ n' → s (r · n' · m))

tdouble-tplus : Term (nat ⇒ nat ⇒ nat)
tdouble-tplus = 2 # λ n m → tdouble · (tplus · n · m)

tplus-tdouble : Term (nat ⇒ nat ⇒ nat)
tplus-tdouble = 2 # λ n m → tplus · (tdouble · n) · (tdouble · m)

tmult : Term (nat ⇒ nat ⇒ nat)
tmult = fix 3 # λ r n m → caseNat n
                   z
                  (1 # λ n' → tplus · m · (r · n' · m))

tmult-tmult : Term (nat ⇒ nat ⇒ nat ⇒ nat)
tmult-tmult = 3 # λ n m p → tmult · (tmult · n · m) · p

tmap-titerate : ∀ {σ} -> Term ((σ ⇒ σ) ⇒ σ ⇒ list σ)
tmap-titerate = 2 # λ f x → tmap · f · (titerate · f · x)

sands : Term (nat ⇒ nat)
sands = fix 2 # λ r n → caseNat n
                  (r · n)
                  (1 # λ _ → s z)

tconcat : ∀ {σ} -> Term (list (list σ) ⇒ list σ)
tconcat = tfoldr · tapp · nil

tconcat-tmap-tconcat : ∀ {σ} -> Term (list (list (list σ)) ⇒ list σ)
tconcat-tmap-tconcat = 1 # λ xs → tconcat · (tmap · tconcat · xs)

id-nat : Term (nat ⇒ nat)
id-nat = fix 2 # λ r n → caseNat n
                    z
                   (1 # λ n' → s (r · n'))

id-nat-id-nat : Term (nat ⇒ nat)
id-nat-id-nat = 1 # λ n → id-nat · (id-nat · n)

caseNat-undefined : Term nat
caseNat-undefined = caseNat undefined z (1 # λ _ → z)

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
scε-tdouble-tplus         =              scε  tdouble-tplus
scε-tplus-tdouble         =              scε  tplus-tdouble

-- Not sure.
scε-tcycle-cons           =              scε (z :: tcycle · (s z :: z :: nil))
scε-tlookup-tzeros        =              scε  tlookup-tzeros
scε-teven-tdouble         =              scε  teven-tdouble

-- sc-sands-·                =              sc {ε ▻ nat} (sands · var vz)

-- Do not terminate.
scε-tmap-titerate         = λ {σ}     -> scε (tmap-titerate {σ})
scε-tconcat-tmap-tconcat  = λ {σ}     -> scε (tconcat-tmap-tconcat {σ})

-- Are these two α-equal?
scε-tfoldr-tapp           = λ {σ τ}   -> scε (tfoldr-tapp   {σ} {τ})
scε-tfoldr-tfoldr         = λ {σ τ}   -> scε (tfoldr-tfoldr {σ} {τ})

scε-tmult2                =              scε  (tmult · s (s z))

-- Hmm:
-- lam "x0"
-- (Let "r1" :=
--  lam "x0"
--  (caseNat (var "x0")
--   (Let "r4" :=
--    lam "x0"
--    (caseNat (var "x0") z
--     (lam "x1" (s (var "r4" · var "x1" · var "x0"))))
--    In (var "r4" · var "x0"))
--   (lam "x1" (s (var "r1" · var "x1" · var "x0"))))
--  In (var "r1" · var "x0"))
