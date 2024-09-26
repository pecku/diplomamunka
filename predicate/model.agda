{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
-- import I

module model
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

data _≡_ {A : Set}(a : A) : A → Prop where
  refl : a ≡ a

infix 4 _≡_

record 𝟙 : Set where

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

-- A ^ n = n hosszu vektor A-elemekkel
_^_ : Set → ℕ → Set
A ^ zero = 𝟙
A ^ (suc n) = A × (A ^ n)

map : ∀{A B n} → (A → B) → A ^ n → B ^ n
map {n = zero}  f _        = _
map {n = suc n} f (a , as) = f a , map f as

-- funar 0 = konstansszimbólumok halmaza
-- funar 1 = 1-paraméteres függvényszimbólumok halmaza
-- funar 2 = 2-paraméteres függvényszimbólumok halmaza
-- ...
-- relar 0 = alapállítások halmaza
-- relar 1 = predikátumszimbólumok halmaza
-- relar 2 = bináris relációszimbólumok halmaza
-- ...

-- pl. Peano aritmetika:
-- funar 0 = 1    zero : Nat
-- funar 1 = 1    suc  : Nat → Nat
-- funar 2 = 3    _+_, _*_, _^_ : Nat → Nat → Nat
-- funar _ = 0
-- relar 0 = 0
-- relar 1 = 0
-- relar 2 = 2    _<_, _=_ : Nat → Nat → Prop

-- 


record Model {i j} : Set (lsuc i ⊔ lsuc j) where
   field
      Con : Set
      For : Con → Set
      Pf  : (Γ : Con) → For Γ → Prop
      Sub : Con → Con → Set
      Tm  : Con → Set

      ◇   : Con
      ε   : ∀{Γ} → Sub Γ ◇
      id  : ∀{Γ} → Sub Γ Γ
      _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      
      _[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
      _[_]ᵖ : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)
      _[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ
      
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      _,ₚ_  : ∀{Δ Γ A} → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ) → Sub Δ (Γ ▹ₚ A)
      pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
      qₚ    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))

      _▹ₜ : Con → Con
      _,ₜ_ : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      qₜ   : ∀{Γ} → Tm (Γ ▹ₜ)
      pₜ   : ∀{Γ} → Sub (Γ ▹ₜ) Γ

      _⊃_   : ∀{Γ} → For Γ → For Γ → For Γ
      ⊃in   : ∀{Γ A B} → Pf (Γ ▹ₚ A) (B [ pₚ ]ᶠ)→ Pf Γ ((A ⊃ B))
      ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B

      _∧_   : ∀{Γ} → For Γ → For Γ → For Γ
      ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
      ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
      ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B

      ⊤     : ∀{Γ} → For Γ
      ⊤in   : ∀{Γ} → Pf Γ ⊤

      _∨_   : ∀{Γ} → For Γ → For Γ → For Γ
      ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
      ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ) → Pf Γ (A ∨ B) → Pf Γ C

      ⊥     : ∀{Γ} → For Γ
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A

      Forall : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
      ∀in : ∀{Γ A} → Pf (Γ ▹ₜ ) A → Pf Γ (Forall A)
      ∀out : ∀{Γ A} → Pf Γ (Forall A) → Pf (Γ ▹ₜ ) A

      -- ∃ : {!   !}
      -- ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
      -- ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) C → Pf Γ (∃ A) → Pf Γ C

      Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ
      Rel[] : ∀{Γ n}{ar : relar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ} → Rel ar ts [ γ ]ᶠ ≡ Rel ar (map _[ γ ]ᵗ ts)

      fun   : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ
      fun[] : ∀{Γ n}{ar : funar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ} → fun ar ts [ γ ]ᵗ ≡ fun ar (map _[ γ ]ᵗ ts)

{-
      Rel : {n : ℕ} → relar n → Tm Γ → Tm Γ → ... → Tm Γ → For Γ
                                \______________________/
                                          n db

      Rel : {n : ℕ} → relar n → For (◇ ▹ₜ ▹ₜ ... ▹ₜ)

      Tms : Con → ℕ → Set

      Rel : {n : ℕ} → relar n → Tms Γ n → For Γ

      Tms Γ 0 ≅ ⊤
      Tms Γ (1+n) ≅ Tms Γ n × Tm Γ
-}

   infixl 5 _▹ₚ_
   infixl 5 _,ₚ_
   infixl 5 _▹ₜ
   infixl 5 _,ₜ_
   infixr 6 _∘_
   infixl 8 _[_]ᶠ
   infixl 8 _[_]ᵖ
   infixl 8 _[_]ᵗ
   infixr 6 _⊃_
   infixr 8 _∧_
   infixr 7 _∨_
