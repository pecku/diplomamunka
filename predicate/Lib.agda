{-# OPTIONS --prop #-}

module Lib where

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.Sigma public

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
   instance refl : a ≡ a

infix 4 _≡_

substP : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Prop ℓ'){a a' : A} → a ≡ a' → P a → P a'
substP P refl p = p

_⁻¹ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl

cong : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong₂ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}
        {a c : A}{b d : B}(f : A → B → C)(p : a ≡ c)(q : b ≡ d) →
        f a b ≡ f c d
cong₂ f refl refl = refl

_◾_ : ∀{ℓ}{A : Set ℓ}{a a' : A} → a ≡ a' → ∀{a''} → a' ≡ a'' → a ≡ a''
refl ◾ refl = refl

infixl 2 _◾_

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

record Lift {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk
  field
    un : A
