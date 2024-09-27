
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
infixr 6 _∘_
infixl 9 _[_]ᶠ
infixl 9 _[_]ᵖ
infixl 9 _[_]ᵗ
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

id : ∀{Γ} → Sub Γ Γ
id {◇}    = ε
id {Γ ▹ₜ} = wkSub (id {Γ}) ,ₜ var vz

p : ∀{Γ} → Sub (Γ ▹ₜ) Γ
p = wkSub id

_⁺ : ∀{Γ Δ} → Sub Δ Γ → Sub (Δ ▹ₜ) (Γ ▹ₜ)
γ ⁺ = wkSub γ ,ₜ var vz

_[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ
_[_]ᵗs : ∀{Γ Δ n} → Tm Γ ^ n → Sub Δ Γ → Tm Δ ^ n

_[_]ᵗs {n = zero}  _        γ = _
_[_]ᵗs {n = suc n} (a , as) γ = a [ γ ]ᵗ , as [ γ ]ᵗs

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
Rel ar ts [ γ ]ᶠ = Rel ar (map _[ γ ]ᵗ ts)

data Conp : Con → Set where
  ◇ₚ : ∀{Γ} → Conp Γ
  _▹ₚ_ : ∀{Γ} → Conp Γ → For Γ → Conp Γ

_[_]Conp : ∀{Γ Δ} → Conp Γ → Sub Δ Γ → Conp Δ
◇ₚ [ γ ]Conp = ◇ₚ
(Γₚ ▹ₚ A) [ γ ]Conp = Γₚ [ γ ]Conp ▹ₚ A [ γ ]ᶠ

data Pf : (Γ : Con)(Γₚ : Conp Γ) → For Γ → Prop

data Subp : (Γ : Con) → Conp Γ → Conp Γ → Prop where
  idp : ∀{Γ Γₚ} → Subp Γ Γₚ Γₚ
  ε  : ∀{Γ Γₚ} → Subp Γ Γₚ ◇ₚ
  _,p_ : ∀{Δ Γₚ Δₚ A} → Subp Δ Δₚ Γₚ → Pf Δ Δₚ A → Subp Δ Δₚ (Γₚ ▹ₚ A)

data Pf where
  _[_]ᵖ : ∀{Γ Γₚ Δ A} → Pf Γ Γₚ A → (γ : Sub Δ Γ) → Pf Δ (Γₚ [ γ ]Conp) (A [ γ ]ᶠ)
  qₚ    : ∀{Γ Γₚ A} → Pf Γ (Γₚ ▹ₚ A) A
  ⊃in   : ∀{Γ Γₚ A B} → Pf Γ (Γₚ ▹ₚ A) B → Pf Γ Γₚ (A ⊃ B)
  ⊃out  : ∀{Γ Γₚ A B} → Pf Γ Γₚ (A ⊃ B) → Pf Γ Γₚ A → Pf Γ Γₚ B
  {-
  ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
  ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
  ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
  ⊤in   : ∀{Γ} → Pf Γ ⊤
  ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
  ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
  ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ) → Pf Γ (A ∨ B) → Pf Γ C
  ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A
  -}
  ∀in : ∀{Γ Γₚ A} → Pf (Γ ▹ₜ) (Γₚ [ p ]Conp) A → Pf Γ Γₚ (Forall A)
  ∀out : ∀{Γ Γₚ A} → Pf Γ Γₚ (Forall A) → Pf (Γ ▹ₜ) (Γₚ [ p ]Conp) A
  {-
  ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
  ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) (C [ pₜ ∘ pₚ ]ᶠ) → Pf Γ (∃ A) → Pf Γ C
  -}

open import model funar relar

M : Model
M = record
     { Con = Σ Con Conp
     ; For = λ (Γ , Γₚ) → For Γ
     ; Pf = {!!}
     ; Sub = λ (Δ , Δₚ) (Γ , Γₚ) → Σ (Sub Δ Γ) λ γ → Lift (Subp Δ Δₚ (Γₚ [ γ ]Conp))
     ; Tm = λ (Γ , Γₚ) → Tm Γ
     ; ◇ = ◇ , ◇ₚ
     ; ε = {!!}
     ; id = {!!}
     ; _∘_ = {!!}
     ; _[_]ᶠ = {!!}
     ; _[_]ᵖ = {!!}
     ; _[_]ᵗ = {!!}
     ; _▹ₚ_ = λ (Γ , Γₚ) A → Γ , Γₚ ▹ₚ A
     ; _,ₚ_ = {!!}
     ; pₚ = {!!}
     ; qₚ = {!!}
     ; _▹ₜ = λ (Γ , Γₚ) → Γ ▹ₜ , Γₚ [ p ]Conp
     ; _,ₜ_ = {!!}
     ; qₜ = {!!}
     ; pₜ = {!!}
     ; _⊃_ = {!!}
     ; ⊃[] = {!!}
     ; ⊃in = {!!}
     ; ⊃out = {!!}
     ; _∧_ = {!!}
     ; ∧[] = {!!}
     ; ∧in = {!!}
     ; ∧out₁ = {!!}
     ; ∧out₂ = {!!}
     ; ⊤ = {!!}
     ; ⊤[] = {!!}
     ; ⊤in = {!!}
     ; _∨_ = {!!}
     ; ∨[] = {!!}
     ; ∨in₁ = {!!}
     ; ∨in₂ = {!!}
     ; ∨out = {!!}
     ; ⊥ = {!!}
     ; ⊥[] = {!!}
     ; ⊥out = {!!}
     ; Forall = {!!}
     ; Forall[] = {!!}
     ; ∀in = {!!}
     ; ∀out = {!!}
     ; ∃ = {!!}
     ; ∃[] = {!!}
     ; ∃in = {!!}
     ; ∃out = {!!}
     ; [∘]ᶠ = {!!}
     ; [id]ᶠ = {!!}
     ; [∘]ᵗ = {!!}
     ; [id]ᵗ = {!!}
     ; ▹ₚβ₁ = {!!}
     ; ▹ₚη = {!!}
     ; ▹ₜβ₁ = {!!}
     ; ▹ₜβ₂ = {!!}
     ; ▹ₜη = {!!}
     ; Rel = {!!}
     ; Rel[] = {!!}
     ; fun = {!!}
     ; fun[] = {!!}
     }

-- TODO: iterator, induction principle
