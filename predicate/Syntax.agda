
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
  ∃ : ∀{Γ} → For (Γ ▹ₜ) → For Γ
  Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ

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

idₜ : ∀{Γ} → Sub Γ Γ
idₜ = ⌜ idV ⌝

pₜ : ∀{Γ} → Sub (Γ ▹ₜ) Γ
pₜ = wkSub idₜ

qₜ : ∀{Γ} → Tm (Γ ▹ₜ)
qₜ = var vz

_⁺ : ∀{Γ Δ} → Sub Δ Γ → Sub (Δ ▹ₜ) (Γ ▹ₜ)
γ ⁺ = wkSub γ ,ₜ var vz

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

_[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
(A ⊃ B) [ γ ]ᶠ = A [ γ ]ᶠ ⊃ B [ γ ]ᶠ
(A ∧ B) [ γ ]ᶠ = A [ γ ]ᶠ ∧ B [ γ ]ᶠ
⊤ [ γ ]ᶠ = ⊤
(A ∨ B) [ γ ]ᶠ = A [ γ ]ᶠ ∨ B [ γ ]ᶠ
⊥ [ γ ]ᶠ = ⊥
Forall A [ γ ]ᶠ = Forall (A [ γ ⁺ ]ᶠ)
∃ A [ γ ]ᶠ = ∃ (A [ γ ⁺ ]ᶠ)
Rel ar ts [ γ ]ᶠ = Rel ar (ts [ γ ]ᵗs)

_∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
ε ∘ s = ε
(s ,ₜ t) ∘ s₁ = s ∘ s₁ ,ₜ t [ s₁ ]ᵗ

▹ₜβ₁ : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → pₜ ∘ (γ ,ₜ t) ≡ γ
▹ₜβ₁ {.◇} {Δ} {t} {ε} = refl
▹ₜβ₁ {.(_ ▹ₜ)} {Δ} {t} {γ ,ₜ x} = {! !} 

⌜⌝⁺≡⌜⁺ᵛ⌝ : ∀{Δ Γ}{γ : VSub Δ Γ} → ⌜ γ ⌝ ⁺ ≡ ⌜ γ ⁺ᵛ ⌝
⌜⌝⁺≡⌜⁺ᵛ⌝ {Δ} {.◇} {ε} = refl
⌜⌝⁺≡⌜⁺ᵛ⌝ {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} = {! cong (pₜ ∘_) (⌜⌝⁺≡⌜⁺ᵛ⌝ {γ = γ}) !}

id+≡id : ∀{Γ} → idₜ {Γ} ⁺ ≡ idₜ
id+≡id = ⌜⌝⁺≡⌜⁺ᵛ⌝

[⌜⌝] : ∀{Δ Γ}{γ : VSub Δ Γ}{x} → var x [ ⌜ γ ⌝ ]ᵗ ≡ var (x [ γ ]vᵗ )
[⌜⌝] {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} {vz} = refl
[⌜⌝] {Δ} {.(_ ▹ₜ)} {γ ,ᵥ x} {vs x₁} = [⌜⌝] {x = x₁}

t[id]ᵗ : ∀{Γ}{t : Tm Γ} → t [ idₜ ]ᵗ ≡ t
t[id]ᵗs : ∀{Γ n}{ts : Tm Γ ^ n} → ts [ idₜ ]ᵗs ≡ ts

t[id]ᵗ {Γ} {var x} = [⌜⌝] {x = x} ◾ cong var ([id]v {x = x})
t[id]ᵗ {Γ} {fun ar ts} = cong (λ x → fun ar x) t[id]ᵗs

t[id]ᵗs {Γ} {zero} {ts} = refl
t[id]ᵗs {Γ} {suc n} {ts} = cong₂ (λ x xs → x , xs) t[id]ᵗ t[id]ᵗs

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
[id]Conp {Γ} {c ▹ₚ A ⊃ B} = cong₂ (λ a b → _ ▹ₚ a ⊃ b) f[id]ᶠ f[id]ᶠ ◾ cong (λ x → x ▹ₚ A ⊃ B) [id]Conp
[id]Conp {Γ} {c ▹ₚ A ∧ B} = cong₂ (λ a b → _ ▹ₚ a ∧ b) f[id]ᶠ f[id]ᶠ ◾ cong (λ x → x ▹ₚ A ∧ B) [id]Conp
[id]Conp {Γ} {c ▹ₚ ⊤} = cong (_▹ₚ ⊤) [id]Conp
[id]Conp {Γ} {c ▹ₚ A ∨ B} = cong₂ (λ a b → _ ▹ₚ a ∨ b) f[id]ᶠ f[id]ᶠ ◾ cong (λ x → x ▹ₚ A ∨ B) [id]Conp
[id]Conp {Γ} {c ▹ₚ ⊥} = cong (_▹ₚ ⊥) [id]Conp
[id]Conp {Γ} {c ▹ₚ Forall A} = cong (λ x → x ▹ₚ Forall (A [ idₜ ⁺ ]ᶠ)) [id]Conp ◾ cong (λ x → c ▹ₚ Forall (A [ x ]ᶠ)) id+≡id ◾ cong (λ x → c ▹ₚ Forall x) f[id]ᶠ
[id]Conp {Γ} {c ▹ₚ ∃ A} = cong (λ x → x ▹ₚ ∃ (A [ idₜ ⁺ ]ᶠ)) [id]Conp ◾ cong (λ x → c ▹ₚ ∃ (A [ x ]ᶠ)) id+≡id ◾ cong (λ x → c ▹ₚ ∃ x) f[id]ᶠ
[id]Conp {Γ} {c ▹ₚ Rel ar A} = cong (λ x → x ▹ₚ Rel ar (A [ idₜ ]ᵗs)) [id]Conp ◾ cong (λ x → c ▹ₚ Rel ar x) t[id]ᵗs

data Pf : (Γ : Con)(Γₚ : Conp Γ) → For Γ → Prop

data Subp : (Γ : Con) → Conp Γ → Conp Γ → Prop where
  idp : ∀{Γ Γₚ} → Subp Γ Γₚ Γₚ
  ε  : ∀{Γ Γₚ} → Subp Γ Γₚ ◇ₚ
  _,ₚ_ : ∀{Δ Γₚ Δₚ A} → Subp Δ Δₚ Γₚ → Pf Δ Δₚ A → Subp Δ Δₚ (Γₚ ▹ₚ A)
  pₚ : ∀{Γ Γₚ A} → Subp Γ (Γₚ ▹ₚ A) (Γₚ [ idₜ ]Conp)

data Pf where
  _[_]ᵖ : ∀{Γ Γₚ Δ A} → Pf Γ Γₚ A → (γ : Sub Δ Γ) → Pf Δ (Γₚ [ γ ]Conp) (A [ γ ]ᶠ)
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
  ∃out : ∀{Γ Γₚ A C} → Pf Γ (Γₚ ▹ₚ A) C → Pf Γ Γₚ (∃ (A [ pₜ ]ᶠ)) → Pf Γ Γₚ C

open import model funar relar

I : Model
I = record
     { Con = Σ Con Conp
     ; For = λ (Γ , Γₚ) → For Γ
     ; Pf = λ (Γ , Γₚ) A → Pf Γ Γₚ A
     ; Sub = λ (Δ , Δₚ) (Γ , Γₚ) → Σ (Sub Δ Γ) λ γ → Lift (Subp Δ Δₚ (Γₚ [ γ ]Conp))
     ; Tm = λ (Γ , Γₚ) → Tm Γ
     ; ◇ = ◇ , ◇ₚ
     ; ε = ε , mk ε
     ; id = λ {(Γ , Γₚ)} → idₜ , mk (substP (λ x → Subp Γ Γₚ x) ([id]Conp ⁻¹) idp)
     ; _∘_ = λ s sₚ → fst s ∘ fst sₚ , mk {! snd sₚ  !}
     ; _[_]ᶠ = λ A (s , sₚ) → A [ s ]ᶠ
     ; _[_]ᵖ = λ p (s , sₚ) → {! p [ s ]ᵖ  !}
     ; _[_]ᵗ = λ t (s , sₚ)  → t [ s ]ᵗ
     ; _▹ₚ_ = λ (Γ , Γₚ) A → Γ , Γₚ ▹ₚ A
     ; _,ₚ_ = λ (s , (mk sₚ)) p → s , mk (sₚ ,ₚ p)
     ; pₚ = idₜ , mk pₚ
     ; qₚ = λ {(Γ , Γₚ)}{A} → substP (λ x → Pf Γ (Γₚ ▹ₚ A) x) (f[id]ᶠ ⁻¹) qₚ
     ; _▹ₜ = λ (Γ , Γₚ) → Γ ▹ₜ , Γₚ [ pₜ ]Conp
     ; _,ₜ_ = λ (Γ , (mk Γₚ)) t → Γ ,ₜ t , mk {! Γₚ  !}
     ; qₜ = qₜ
     ; pₜ = wkSub idₜ , mk {!  !}
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
     ; Forall[] = {!!}
     ; ∀in = ∀in
     ; ∀out = ∀out
     ; ∃ = ∃
     ; ∃[] = {!!}
     ; ∃in = ∃in
     ; ∃out = λ {(Γ , Γₚ) A C} → {!∃out {Γ}!}
     ; [∘]ᶠ = {!!}
     ; [id]ᶠ = f[id]ᶠ
     ; [∘]ᵗ = {!!}
     ; [id]ᵗ = t[id]ᵗ
     ; ▹ₚβ₁ = {!!}
     ; ▹ₚη = {!!}
     ; ▹ₜβ₁ = {!!}
     ; ▹ₜβ₂ = {!!}
     ; ▹ₜη = {!!}
     ; Rel = Rel 
     ; Rel[] = λ {Γ n ar} → cong (λ x → Rel ar x) s≡map
     ; fun = fun
     ; fun[] = λ {Γ n ar} → cong (λ x → fun ar x) s≡map
     } 
 
-- TODO: iterator, induction principle
                              