
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
data Pf   : (Γ : Con) → For Γ → Prop
data Sub  : Con → Con → Set
data Tm   : Con → Set

data Con where
     ◇    : Con
     _▹ₚ_ : (Γ : Con) → For Γ → Con
     _▹ₜ  : Con → Con

data For where
     _⊃_   : ∀{Γ} → For Γ → For Γ → For Γ
     _∧_   : ∀{Γ} → For Γ → For Γ → For Γ
     ⊤     : ∀{Γ} → For Γ
     _∨_   : ∀{Γ} → For Γ → For Γ → For Γ
     ⊥     : ∀{Γ} → For Γ
     Forall : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
     ∃ : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
     Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ

data VTm : Con → Set where
  vz : ∀{Γ} → VTm (Γ ▹ₜ)
  vs : ∀{Γ} → VTm Γ → VTm (Γ ▹ₜ)

data Tm where
  var : ∀{Γ} → VTm Γ → Tm Γ
  fun : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ

data VSub : Con → Con → Set
_[_]Vᶠ : ∀{Γ Δ} → For Γ → VSub Δ Γ → For Δ

data VSub where
  ε     : ∀{Γ} → VSub Γ ◇
  _,ₜ_  : ∀{Γ Δ} → VSub Δ Γ → VTm Δ → VSub Δ (Γ ▹ₜ)
  _,ₚ_  : ∀{Δ Γ A} → (γ : VSub Δ Γ) → Pf Δ (A [ γ ]Vᶠ) → VSub Δ (Γ ▹ₚ A)

{- ezeknek mind kell a V-s valtozata
pₜ    : ∀{Γ} → Sub (Γ ▹ₜ) Γ
pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
_∘_   : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
id    : ∀{Γ} → Sub Γ Γ
qₜ    : ∀{Γ} → Tm (Γ ▹ₜ)
_[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ
-}

_[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ

_[_]ᵖ' : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)

wkVₜ : ∀{Γ Δ} → VSub Δ Γ → VSub (Δ ▹ₜ) Γ
wkVₜ ε = ε
wkVₜ (γ ,ₜ t) = wkVₜ γ ,ₜ vs t
wkVₜ (γ ,ₚ a) = wkVₜ γ ,ₚ {!!}

wkVₚ : ∀{Γ Δ A} → VSub Δ Γ → VSub (Δ ▹ₚ A) Γ
wkVₚ = {!!}

qₚ'    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))

idV : ∀{Γ} → VSub Γ Γ
idV {◇} = ε
idV {Γ ▹ₚ A} = wkVₚ (idV {Γ}) ,ₚ {!!}
idV {Γ ▹ₜ} = wkVₜ (idV {Γ}) ,ₜ vz

-- wkV : VSub Δ Γ → VSub (Δ ▹ₚ A) Γ


data Sub where
  ε     : ∀{Γ} → Sub Γ ◇
  _,ₜ_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
  _,ₚ_  : ∀{Δ Γ A} → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ) → Sub Δ (Γ ▹ₚ A)

pₜ    : ∀{Γ} → Sub (Γ ▹ₜ) Γ
pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
_∘_   : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
id    : ∀{Γ} → Sub Γ Γ
qₜ    : ∀{Γ} → Tm (Γ ▹ₜ)
_[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ

(A ⊃ B) [ γ ]ᶠ = A [ γ ]ᶠ ⊃ B [ γ ]ᶠ
(A ∧ B) [ γ ]ᶠ = A [ γ ]ᶠ ∧ B [ γ ]ᶠ
⊤ [ γ ]ᶠ = ⊤
(A ∨ B) [ γ ]ᶠ = A [ γ ]ᶠ ∨ B [ γ ]ᶠ
⊥ [ γ ]ᶠ = ⊥
Forall A [ γ ]ᶠ = Forall (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
∃ A [ γ ]ᶠ = {!!}
Rel ar ts [ γ ]ᶠ = Rel ar (map (_[ γ ]ᵗ) ts )

data Pf where
     _[_]ᵖ : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)
     qₚ    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))
     ⊃in   : ∀{Γ A B} → Pf (Γ ▹ₚ A) (B [ pₚ ]ᶠ)→ Pf Γ ((A ⊃ B))
     ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B
     ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
     ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
     ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
     ⊤in   : ∀{Γ} → Pf Γ ⊤
     ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
     ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
     ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ) → Pf Γ (A ∨ B) → Pf Γ C
     ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A
     ∀in : ∀{Γ A} → Pf (Γ ▹ₜ ) A → Pf Γ (Forall A)
     ∀out : ∀{Γ A} → Pf Γ (Forall A) → Pf (Γ ▹ₜ ) A
     ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
     ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) (C [ pₜ ∘ pₚ ]ᶠ) → Pf Γ (∃ A) → Pf Γ C

_[_]ᵖ' = _[_]ᵖ
qₚ' = qₚ
