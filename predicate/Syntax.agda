
{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib

module Syntax
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

-- lasd meg: bitbucket.org/akaposi/logic, itt FirstOrderFinitary

-- ugyanaz, mint a modell, csak minden data-val adunk meg, kiveve _∘_, _[_]ᶠ,_[_]ᵗ-ket.

infixl 5 _▹ₚ_
infixl 5 _,ₚ_
infixl 5 _▹ₜ
infixl 5 _,ₜ_
infixl 5 _,ᵥ_
infixr 6 _∘_
infixl 9 _[_]ᶠ
infixl 9 _[_]ᵖ
infixl 9 _[_]ᵗ
infixl 9 _[_]vᵗ
infixr 6 _⊃_
infixr 8 _∧_
infixr 7 _∨_

data Con  : Set
data For  : Con → Set
data Sub  : Con → Con → Set
data Tm   : Con → Set

data Con where
  ◇    : Con
  _▹ₜ  : Con → Con

data For where
  _⊃_   : ∀{Γ} → For Γ → For Γ → For Γ
  _∧_   : ∀{Γ} → For Γ → For Γ → For Γ
  ⊤     : ∀{Γ} → For Γ
  _∨_   : ∀{Γ} → For Γ → For Γ → For Γ
  ⊥     : ∀{Γ} → For Γ
  Forall : ∀{Γ} → For (Γ ▹ₜ) → For Γ
  ∃      : ∀{Γ} → For (Γ ▹ₜ) → For Γ
  Rel    : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ

data VTm : Con → Set where
  vz : ∀{Γ} → VTm (Γ ▹ₜ)
  vs : ∀{Γ} → VTm Γ → VTm (Γ ▹ₜ)

data VSub : Con → Con → Set where
  ε     : ∀{Γ} → VSub Γ ◇
  _,ᵥ_ : ∀{Γ Δ} → VSub Δ Γ → VTm Δ → VSub Δ (Γ ▹ₜ)

_[_]vᵗ : ∀{Γ Δ} → VTm Γ → VSub Δ Γ → VTm Δ
vz [ s ,ᵥ x ]vᵗ = x
vs x [ s ,ᵥ _ ]vᵗ = x [ s ]vᵗ

wkVSub : ∀{Γ Δ} → VSub Δ Γ → VSub (Δ ▹ₜ) Γ
wkVSub ε        = ε
wkVSub (γ ,ᵥ x) = wkVSub γ ,ᵥ vs x

idV : ∀{Γ} → VSub Γ Γ
idV {◇}    = ε
idV {Γ ▹ₜ} = wkVSub (idV {Γ}) ,ᵥ vz

pᵥ : ∀{Γ} → VSub (Γ ▹ₜ) Γ
pᵥ = wkVSub idV

wkvs : ∀{Δ Γ}{γ : VSub Δ Γ}{x} → x [ wkVSub γ ]vᵗ ≡ vs (x [ γ ]vᵗ)
wkvs {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} {vz} = refl
wkvs {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x₁} {vs x} = wkvs {x = x}

[id]v : ∀{Γ}{x : VTm Γ} → x [ idV ]vᵗ ≡ x
[id]v {x = vz} = refl
[id]v {x = vs x} = wkvs {γ = idV} {x = x} ◾ cong vs ([id]v {x = x})

_⁺ᵛ : ∀{Γ Δ} → VSub Δ Γ → VSub (Δ ▹ₜ) (Γ ▹ₜ)
γ ⁺ᵛ = wkVSub γ ,ᵥ vz

data Tm where
  var : ∀{Γ} → VTm Γ → Tm Γ
  fun : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ

data Sub where
  ε     : ∀{Γ} → Sub Γ ◇
  _,ₜ_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)

◇η  : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε
◇η {Γ} {ε} = refl

inj-,ₜ : ∀{Γ Δ}{γ γ' : Sub Δ Γ}{t t'} → γ ,ₜ t ≡ γ' ,ₜ t' → γ ≡ γ'
inj-,ₜ refl = refl

wkₜ  : ∀{Γ} → Tm Γ → Tm (Γ ▹ₜ)
wkₜs : ∀{Γ n} → Tm Γ ^ n → Tm (Γ ▹ₜ) ^ n

wkₜs {n = zero}  _        = _
wkₜs {n = suc n} (t , ts) = wkₜ t , wkₜs ts

wkₜ (var x) = var (vs x)
wkₜ (fun ar ts) = fun ar (wkₜs ts)

wkSub : ∀{Γ Δ} → Sub Δ Γ → Sub (Δ ▹ₜ) Γ
wkSub ε        = ε
wkSub (γ ,ₜ t) = wkSub γ ,ₜ wkₜ t

⌜_⌝ : ∀{Δ Γ} → VSub Δ Γ → Sub Δ Γ
⌜ ε ⌝ = ε
⌜ γ ,ᵥ x ⌝ = ⌜ γ ⌝ ,ₜ var x

⌜wkSub⌝ : ∀{Γ Δ}{γ : VSub Δ Γ} → ⌜ wkVSub γ ⌝ ≡ wkSub ⌜ γ ⌝
⌜wkSub⌝ {γ = ε} = refl
⌜wkSub⌝ {γ = γ ,ᵥ t} = cong (_,ₜ var (vs t)) (⌜wkSub⌝ {γ = γ})

idₜ : ∀{Γ} → Sub Γ Γ
idₜ = ⌜ idV ⌝

pₜ : ∀{Γ} → Sub (Γ ▹ₜ) Γ
pₜ = ⌜ pᵥ ⌝

qₜ : ∀{Γ} → Tm (Γ ▹ₜ)
qₜ = var vz

_⁺ : ∀{Γ Δ} → Sub Δ Γ → Sub (Δ ▹ₜ) (Γ ▹ₜ)
γ ⁺ = wkSub γ ,ₜ qₜ

_[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ

_[_]ᵗs : ∀{Γ Δ n} → Tm Γ ^ n → Sub Δ Γ → Tm Δ ^ n

_[_]ᵗs {n = zero}  _        γ = _
_[_]ᵗs {n = suc n} (a , as) γ = a [ γ ]ᵗ , as [ γ ]ᵗs

s≡map : ∀{Δ Γ}{γ : Sub Δ Γ}{n}{ts : Tm Γ ^ n} → ts [ γ ]ᵗs ≡ map (_[ γ ]ᵗ) ts
s≡map {Δ} {Γ} {γ} {zero} {ts} = refl
s≡map {Δ} {Γ} {γ} {suc n} {t , ts} = cong (λ x → (t [ γ ]ᵗ , x)) s≡map

var vz [ γ ,ₜ a ]ᵗ = a
var (vs x) [ γ ,ₜ a ]ᵗ = var x [ γ ]ᵗ
fun ar ts [ γ ]ᵗ = fun ar (ts [ γ ]ᵗs)

_∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
ε ∘ s = ε
(s ,ₜ t) ∘ s₁ = s ∘ s₁ ,ₜ t [ s₁ ]ᵗ

[∘]ᵗ  : ∀{Γ Δ θ}{t : Tm Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ} → t [ γ ∘ δ ]ᵗ ≡ t [ γ ]ᵗ [ δ ]ᵗ
[∘]ᵗs  : ∀{Γ Δ θ n}{ts : Tm Γ ^ n}{γ : Sub Δ Γ}{δ : Sub θ Δ} → ts [ γ ∘ δ ]ᵗs ≡ ts [ γ ]ᵗs [ δ ]ᵗs

[∘]ᵗs {n = zero} = refl
[∘]ᵗs {n = suc n} {t , ts} = cong₂ (_,_) ([∘]ᵗ {t = t}) [∘]ᵗs

[∘]ᵗ {t = var vz} {γ = γ ,ₜ t} = refl
[∘]ᵗ {t = var (vs x)}{γ = γ ,ₜ t} = [∘]ᵗ {t = var x}
[∘]ᵗ {t = fun ar ts} = cong (fun ar) [∘]ᵗs

ass : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
ass {γ = ε} {δ = δ} {θ = θ} = refl
ass {γ = γ ,ₜ t} {δ = δ} {θ = θ} = cong (_,ₜ t [ δ ]ᵗ [ θ ]ᵗ) ass ◾ cong (γ ∘ δ ∘ θ ,ₜ_) ([∘]ᵗ {t = t}{γ = δ}{δ = θ} ⁻¹)

_[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
(A ⊃ B) [ γ ]ᶠ = A [ γ ]ᶠ ⊃ B [ γ ]ᶠ
(A ∧ B) [ γ ]ᶠ = A [ γ ]ᶠ ∧ B [ γ ]ᶠ
⊤ [ γ ]ᶠ = ⊤
(A ∨ B) [ γ ]ᶠ = A [ γ ]ᶠ ∨ B [ γ ]ᶠ
⊥ [ γ ]ᶠ = ⊥
Forall A [ γ ]ᶠ = Forall (A [ γ ⁺ ]ᶠ)
∃ A [ γ ]ᶠ = ∃ (A [ γ ⁺ ]ᶠ)
Rel ar ts [ γ ]ᶠ = Rel ar (ts [ γ ]ᵗs)

wkvar : ∀{Γ Δ}{γ : Sub Δ Γ}{x : VTm Γ} → wkₜ (var x [ γ ]ᵗ) ≡ var x [ wkSub γ ]ᵗ
wkvar {.(_ ▹ₜ)} {Δ} {γ ,ₜ x} {vz} = refl
wkvar {.(_ ▹ₜ)} {Δ} {γ ,ₜ x₁} {vs x} = wkvar {γ = γ} {x = x}

wkx+ : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm Γ} → wkₜ (t [ γ ]ᵗ) ≡ wkₜ t [ γ ⁺ ]ᵗ

wkx+s : ∀{Γ Δ n}{γ : Sub Δ Γ}{ts : Tm Γ ^ n} → wkₜs (ts [ γ ]ᵗs) ≡ wkₜs ts [ γ ⁺ ]ᵗs
wkx+s {n = zero} = refl
wkx+s {n = suc n} {ts = t , ts} = cong₂ (_,_) (wkx+ {t = t}) wkx+s

wkx+ {t = var x} = wkvar {x = x}
wkx+ {t = fun ar ts} = cong (fun ar) wkx+s

wk∘+ : ∀{Γ Δ Θ}{γ : Sub Δ Γ} {δ : Sub Θ Δ} → wkSub (γ ∘ δ) ≡ wkSub γ ∘ (δ ⁺)
wk∘+ {γ = ε} = refl
wk∘+ {γ = γ ,ₜ t} {δ} = cong (_,ₜ wkₜ (t [ δ ]ᵗ)) wk∘+ ◾ cong (wkSub γ ∘ (δ ⁺) ,ₜ_) ((wkx+ {γ = δ}{t = t}))

[∘]ᶠ : ∀{Γ Δ θ}{A : For Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ} → A [ γ ∘ δ ]ᶠ ≡ A [ γ ]ᶠ [ δ ]ᶠ
[∘]ᶠ {A = A ⊃ A₁} = cong₂ _⊃_ [∘]ᶠ [∘]ᶠ
[∘]ᶠ {A = A ∧ A₁} = cong₂ _∧_ [∘]ᶠ [∘]ᶠ
[∘]ᶠ {A = ⊤} = refl
[∘]ᶠ {A = A ∨ A₁} = cong₂ _∨_ [∘]ᶠ [∘]ᶠ
[∘]ᶠ {A = ⊥} = refl
[∘]ᶠ {A = Forall A} = cong Forall (cong (λ z → A [ z ,ₜ var vz ]ᶠ) wk∘+ ◾ [∘]ᶠ {A = A})
[∘]ᶠ {A = ∃ A} = cong ∃ (cong (λ z → A [ z ,ₜ var vz ]ᶠ) wk∘+ ◾ [∘]ᶠ {A = A})
[∘]ᶠ {A = Rel ar ts} = cong (Rel ar) [∘]ᵗs

⌜wk⌝∘ : ∀{Γ Δ}{γ : VSub Δ Γ}{Θ}{δ : Sub Θ Δ}{t : Tm Θ} → ⌜ wkVSub γ ⌝ ∘ (δ ,ₜ t) ≡ ⌜ γ ⌝ ∘ δ
⌜wk⌝∘ {γ = ε} = refl
⌜wk⌝∘ {Γ ▹ₜ}{γ = γ ,ᵥ x}{δ = δ} = cong (_,ₜ var x [ δ ]ᵗ) (⌜wk⌝∘ {Γ = Γ}{γ = γ})

idl : ∀{Γ Δ}{γ : Sub Δ Γ} → idₜ ∘ γ ≡ γ
idl {γ = ε} = refl
idl {Γ ▹ₜ}{γ = γ ,ₜ t} = cong (_,ₜ t) ((⌜wk⌝∘ {γ = idV}) ◾ (idl {Γ}))

▹ₜβ₁ : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → pₜ ∘ (γ ,ₜ t) ≡ γ
▹ₜβ₁ = ⌜wk⌝∘ ◾ idl

▹ₜη : ∀{Γ Δ} → {γt : Sub Δ (Γ ▹ₜ)} → γt ≡ (pₜ ∘ γt ,ₜ qₜ [ γt ]ᵗ)
▹ₜη {γt = γt ,ₜ x} = cong (_,ₜ x) ▹ₜβ₁ ⁻¹

⌜⌝⁺≡⌜⁺ᵛ⌝ : ∀{Δ Γ}{γ : VSub Δ Γ} → ⌜ γ ⌝ ⁺ ≡ ⌜ γ ⁺ᵛ ⌝
⌜⌝⁺≡⌜⁺ᵛ⌝ {Δ} {Γ} {ε} = refl
⌜⌝⁺≡⌜⁺ᵛ⌝ {Δ} {Γ ▹ₜ} {γ ,ᵥ x} = cong (λ z → z ,ₜ var (vs x) ,ₜ var vz) (inj-,ₜ (⌜⌝⁺≡⌜⁺ᵛ⌝ {γ = γ})) 

id+≡id : ∀{Γ} → idₜ {Γ} ⁺ ≡ idₜ
id+≡id = ⌜⌝⁺≡⌜⁺ᵛ⌝

[⌜⌝] : ∀{Δ Γ}{γ : VSub Δ Γ}{x} → var x [ ⌜ γ ⌝ ]ᵗ ≡ var (x [ γ ]vᵗ )
[⌜⌝] {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} {vz} = refl
[⌜⌝] {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} {vs x₁} = [⌜⌝] {x = x₁}

t[id]ᵗ : ∀{Γ}{t : Tm Γ} → t [ idₜ ]ᵗ ≡ t
t[id]ᵗs : ∀{Γ n}{ts : Tm Γ ^ n} → ts [ idₜ ]ᵗs ≡ ts

t[id]ᵗ {Γ} {var x} = [⌜⌝] {x = x} ◾ cong var ([id]v {x = x})
t[id]ᵗ {Γ} {fun ar ts} = cong (fun ar) t[id]ᵗs

t[id]ᵗs {Γ} {zero} {ts} = refl
t[id]ᵗs {Γ} {suc n} {ts} = cong₂ (λ x xs → x , xs) t[id]ᵗ t[id]ᵗs

idr : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ∘ idₜ ≡ γ
idr {γ = ε} = refl
idr {γ = γ ,ₜ x} = cong₂ _,ₜ_ idr t[id]ᵗ

[p] : ∀{Γ}{t : Tm Γ} → t [ pₜ ]ᵗ ≡ wkₜ t
[p]s : ∀{Γ n}{ts : Tm Γ ^ n} → ts [ pₜ ]ᵗs ≡ wkₜs ts
[p] {Γ}{t = var x} = [⌜⌝] {γ = pᵥ {Γ}}{x} ◾ cong var (wkvs {γ = idV}{x = x} ◾ cong vs ([id]v {x = x}))
[p] {t = fun i ts} = cong (fun i) ([p]s {ts = ts})
[p]s {n = zero} {ts} = refl
[p]s {n = suc n} {t , ts} = cong₂ _,_ ([p] {t = t}) ([p]s {ts = ts})

∘p : ∀{Δ Γ}{γ : Sub Δ Γ} → γ ∘ pₜ ≡ wkSub γ
∘p {γ = ε} = refl
∘p {γ = γ ,ₜ t} = cong₂ _,ₜ_ (∘p {γ = γ}) ([p] {t = t})

f[id]ᶠ : ∀{Γ}{A : For Γ} → A [ idₜ ]ᶠ ≡ A
f[id]ᶠ {Γ} {A ⊃ B} = cong₂ (λ a b → a ⊃ b) f[id]ᶠ f[id]ᶠ
f[id]ᶠ {Γ} {A ∧ B} = cong₂ (λ a b → a ∧ b) f[id]ᶠ f[id]ᶠ
f[id]ᶠ {Γ} {⊤} = refl
f[id]ᶠ {Γ} {A ∨ B} = cong₂ (λ a b → a ∨ b) f[id]ᶠ f[id]ᶠ
f[id]ᶠ {Γ} {⊥} = refl
f[id]ᶠ {Γ} {Forall A} = cong (λ a → Forall a) (cong (λ x → A [ x ]ᶠ) id+≡id ◾ f[id]ᶠ)
f[id]ᶠ {Γ} {∃ A} = cong (λ a → ∃ a) (cong (λ x → A [ x ]ᶠ) id+≡id ◾ f[id]ᶠ)
f[id]ᶠ {Γ} {Rel ar ts} = cong (λ x → Rel ar x) t[id]ᵗs

data Conp : Con → Set where
  ◇ₚ : ∀{Γ} → Conp Γ
  _▹ₚ_ : ∀{Γ} → Conp Γ → For Γ → Conp Γ

_[_]Conp : ∀{Γ Δ} → Conp Γ → Sub Δ Γ → Conp Δ
◇ₚ [ γ ]Conp = ◇ₚ
(Γₚ ▹ₚ A) [ γ ]Conp = Γₚ [ γ ]Conp ▹ₚ A [ γ ]ᶠ

[id]Conp : ∀{Γ}{c : Conp Γ} → c [ idₜ ]Conp ≡ c
[id]Conp {Γ} {◇ₚ} = refl
[id]Conp {Γ} {c ▹ₚ A} = cong₂ (_▹ₚ_) [id]Conp f[id]ᶠ

[∘]Conp : ∀{Γ Δ Θ}{Δₚ : Conp Γ}{γ : Sub Δ Γ}{δ : Sub Θ Δ} → Δₚ [ γ ∘ δ ]Conp ≡ Δₚ [ γ ]Conp [ δ ]Conp
[∘]Conp {Δₚ = ◇ₚ} = refl
[∘]Conp {Δₚ = Δₚ ▹ₚ A} = cong₂ (_▹ₚ_) [∘]Conp [∘]ᶠ

data Pf : (Γ : Con)(Γₚ : Conp Γ) → For Γ → Prop

data Subp : (Γ : Con) → Conp Γ → Conp Γ → Prop where
  idp : ∀{Γ Γₚ} → Subp Γ Γₚ Γₚ
  ε  : ∀{Γ Γₚ} → Subp Γ Γₚ ◇ₚ
  _,ₚ_ : ∀{Δ Γₚ Δₚ A} → Subp Δ Δₚ Γₚ → Pf Δ Δₚ A → Subp Δ Δₚ (Γₚ ▹ₚ A)
  pₚ : ∀{Γ Γₚ A} → Subp Γ (Γₚ ▹ₚ A) (Γₚ [ idₜ ]Conp)
  _∘ₚ_ : ∀{Ξ Θₚ Δₚ Γₚ} → Subp Ξ Δₚ Γₚ → Subp Ξ Θₚ Δₚ → Subp Ξ Θₚ Γₚ
  _[_]ᵖ : ∀{Ξ Ψ Δₚ Γₚ} → Subp Ξ Δₚ Γₚ → (ξ : Sub Ψ Ξ) → Subp Ψ (Δₚ [ ξ ]Conp) (Γₚ [ ξ ]Conp)

data Pf where
  _[_]ᵖ  : ∀{Γ Γₚ Δ A} → Pf Γ Γₚ A → (γ : Sub Δ Γ) → Pf Δ (Γₚ [ γ ]Conp) (A [ γ ]ᶠ)
  _[_]ᵖᵖ : ∀{Ξ Γₚ Δₚ A} → Pf Ξ Γₚ A → (γₚ : Subp Ξ Δₚ Γₚ) → Pf Ξ Δₚ A
  qₚ    : ∀{Γ Γₚ A} → Pf Γ (Γₚ ▹ₚ A) A
  ⊃in   : ∀{Γ Γₚ A B} → Pf Γ (Γₚ ▹ₚ A) B → Pf Γ Γₚ (A ⊃ B)
  ⊃out  : ∀{Γ Γₚ A B} → Pf Γ Γₚ (A ⊃ B) → Pf Γ Γₚ A → Pf Γ Γₚ B
  ∧in   : ∀{Γ Γₚ A B} → Pf Γ Γₚ A → Pf Γ Γₚ B → Pf Γ Γₚ (A ∧ B)
  ∧out₁ : ∀{Γ Γₚ A B} → Pf Γ Γₚ  (A ∧ B) → Pf Γ Γₚ A
  ∧out₂ : ∀{Γ Γₚ A B} → Pf Γ Γₚ (A ∧ B) → Pf Γ Γₚ B
  ⊤in   : ∀{Γ Γₚ} → Pf Γ Γₚ ⊤
  ∨in₁  : ∀{Γ Γₚ A B} → Pf Γ Γₚ A → Pf Γ Γₚ (A ∨ B)
  ∨in₂  : ∀{Γ Γₚ A B} → Pf Γ Γₚ B → Pf Γ Γₚ (A ∨ B)
  ∨out  : ∀{Γ Γₚ A B C} → Pf Γ (Γₚ ▹ₚ A) (C) → Pf Γ (Γₚ ▹ₚ B) (C) → Pf Γ Γₚ (A ∨ B) → Pf Γ Γₚ C
  ⊥out  : ∀{Γ Γₚ A} → Pf Γ Γₚ ⊥ → Pf Γ Γₚ A
  ∀in : ∀{Γ Γₚ A} → Pf (Γ ▹ₜ) (Γₚ [ pₜ ]Conp) A → Pf Γ Γₚ (Forall A)
  ∀out : ∀{Γ Γₚ A} → Pf Γ Γₚ (Forall A) → Pf (Γ ▹ₜ) (Γₚ [ pₜ ]Conp) A
  ∃in : ∀{Γ Γₚ A} → (t : Tm Γ) → Pf Γ Γₚ (A [ idₜ ,ₜ t ]ᶠ) → Pf Γ Γₚ (∃ A)
  ∃out : ∀{Γ Γₚ A C} → Pf (Γ ▹ₜ) (Γₚ [ pₜ ]Conp ▹ₚ A) (C [ pₜ ]ᶠ) → Pf Γ Γₚ (∃ A) → Pf Γ Γₚ C

cong, : ∀{Δ Γ Δₚ Γₚ}{γ γ' : Sub Δ Γ}{γₚ : Subp Δ Δₚ (Γₚ [ γ ]Conp)}{γ'ₚ : Subp Δ Δₚ (Γₚ [ γ' ]Conp)} → γ ≡ γ' → (γ , mk γₚ) ≡ (γ' , mk γ'ₚ)
cong, refl = refl

open import model funar relar

I : Model -- {lzero} {lzero}
I = record
  { Con = Σ Con Conp
  ; Sub = λ (Δ , Δₚ) (Γ , Γₚ) → Σ (Sub Δ Γ) λ γ → Lift (Subp Δ Δₚ (Γₚ [ γ ]Conp))
  ; _∘_ = λ {(Γ , Γₚ) (Δ , Δₚ) (Θ , Θₚ)}(γ , mk γₚ) (δ , mk δₚ) → (γ ∘ δ) , mk (substP (Subp Θ Θₚ) ([∘]Conp ⁻¹) ((γₚ [ δ ]ᵖ) ∘ₚ δₚ))
  ; ass = cong, ass
  ; id = λ {(Γ , Γₚ)} → idₜ , mk (substP (λ x → Subp Γ Γₚ x) ([id]Conp ⁻¹) idp)
  ; idl = cong, idl
  ; idr = cong, idr
  ; ◇ = ◇ , ◇ₚ
  ; ε = ε , mk ε
  ; ◇η = cong (_, mk _) ◇η
  ; Tm = λ (Γ , Γₚ) → Tm Γ
  ; _[_]ᵗ = λ t (s , sₚ)  → t [ s ]ᵗ
  ; [∘]ᵗ = λ {Γ Δ Θ t (γ , γₚ) (δ , δₚ)} → [∘]ᵗ {t = t}
  ; [id]ᵗ = t[id]ᵗ
  ; _▹ₜ = λ (Γ , Γₚ) → Γ ▹ₜ , Γₚ [ pₜ ]Conp
  ; _,ₜ_ = λ (γ , mk γₚ) t → (γ ,ₜ t) , mk (substP (Subp _ _) (cong (_ [_]Conp) (▹ₜβ₁ ⁻¹) ◾ [∘]Conp) γₚ)
  ; pₜ = pₜ , mk idp
  ; qₜ = qₜ
  ; ▹ₜβ₁ = cong, ▹ₜβ₁
  ; ▹ₜβ₂ = refl
  ; ▹ₜη = cong, ▹ₜη
  ; For = λ (Γ , Γₚ) → For Γ
  ; _[_]ᶠ = λ A (s , sₚ) → A [ s ]ᶠ
  ; [∘]ᶠ = [∘]ᶠ
  ; [id]ᶠ = f[id]ᶠ
  ; Pf = λ (Γ , Γₚ) A → Pf Γ Γₚ A
  ; _[_]ᵖ = λ { {Γ , Γₚ}{Δ , Δₚ}{A} a (γ , mk γₚ) → (a [ γ ]ᵖ) [ γₚ ]ᵖᵖ }
  ; _▹ₚ_ = λ (Γ , Γₚ) A → Γ , Γₚ ▹ₚ A
  ; _,ₚ_ = λ (s , (mk sₚ)) p → s , mk (sₚ ,ₚ p)
  ; pₚ = idₜ , mk pₚ
  ; qₚ = λ {(Γ , Γₚ)}{A} → substP (λ x → Pf Γ (Γₚ ▹ₚ A) x) (f[id]ᶠ ⁻¹) qₚ
  ; ▹ₚβ₁ = cong, idl
  ; ▹ₚη = cong, idl ⁻¹
  ; Rel = Rel 
  ; Rel[] = λ {Γ n ar} → cong (λ x → Rel ar x) s≡map
  ; fun = fun
  ; fun[] = λ {Γ n ar} → cong (λ x → fun ar x) s≡map
  ; _⊃_ = _⊃_
  ; ⊃[] = refl
  ; ⊃in = λ {(Γ , Γₚ) A B} → substP (λ x → Pf Γ (Γₚ ▹ₚ A) x → Pf Γ Γₚ (A ⊃ B)) (f[id]ᶠ ⁻¹) (⊃in)
  ; ⊃out = ⊃out
  ; _∧_ = _∧_
  ; ∧[] = refl
  ; ∧in = ∧in
  ; ∧out₁ = ∧out₁
  ; ∧out₂ = ∧out₂
  ; ⊤ = ⊤
  ; ⊤[] = refl
  ; ⊤in = ⊤in
  ; _∨_ = _∨_
  ; ∨[] = refl
  ; ∨in₁ = ∨in₁
  ; ∨in₂ = ∨in₂
  ; ∨out =  λ {(Γ , Γₚ)} {A} {B} {C} a b → substP (λ C → Pf Γ Γₚ (A ∨ B) → Pf Γ Γₚ C) f[id]ᶠ (∨out a b)
  ; ⊥ = ⊥
  ; ⊥[] = refl
  ; ⊥out = ⊥out
  ; Forall = Forall
  ; Forall[] = cong (λ z → Forall (_ [ z ,ₜ var vz ]ᶠ)) (∘p ⁻¹)
  ; ∀in = ∀in
  ; ∀out = ∀out
  ; ∃ = ∃
  ; ∃[] = cong (λ z → ∃ (_ [ z ,ₜ var vz ]ᶠ)) (∘p ⁻¹)
  ; ∃in = ∃in
  ; ∃out = λ {(Γ , Γₚ)}{A}{C} w p → ∃out {Γ}{Γₚ}{A}{C} (substP (λ z → Pf (Γ ▹ₜ) ((Γₚ [ pₜ ]Conp) ▹ₚ A) (C [ z ]ᶠ)) idr w) p
  }

-- TODO: iterator, induction principle
