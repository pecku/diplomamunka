{-# OPTIONS --prop #-}

module Lib where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat public renaming (Nat to ℕ) public
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

record 𝟙 {i} : Set i where

_×_ : ∀{i j} → Set i → Set j → Set _
A × B = Σ A λ _ → B

-- A ^ n = n hosszu vektor A-elemekkel
_^_ : ∀{i} → Set i → ℕ → Set i
A ^ zero = 𝟙
A ^ (suc n) = A × (A ^ n)

map : ∀{i}{A B : Set i}{n} → (A → B) → A ^ n → B ^ n
map {n = zero}  f _        = _
map {n = suc n} f (a , as) = f a , map f as

map∘ : ∀{i}{A B C : Set i}{n}{f : A → B}{g : B → C}{as : A ^ n} → map (λ a → g (f a)) as ≡ map g (map f as)
map∘ {n = zero} = refl
map∘ {n = suc n} = cong₂ _,_ refl (map∘ {n = n})

record Lift {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk
  field
    un : A
open Lift public

postulate
  funext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g

-- propositions

record Σp {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,p_
  field
    fst : A
    snd : B fst
open Σp public
infixr 4 _,p_

_×p_ : ∀{i j} → Prop i → Prop j → Prop _
A ×p B = Σp A λ _ → B

data 𝟘p : Prop where

exfalsop : {A : Prop} → 𝟘p → A
exfalsop ()

data 𝟙p : Prop where
  tt : 𝟙p

data _⊎p_ (A B : Prop) : Prop where
  inl : A → A ⊎p B
  inr : B → A ⊎p B

casep : {A B C : Prop} → (A → C) → (B → C) → A ⊎p B → C
casep f g (inl a) = f a
casep f g (inr b) = g b

data Σsp (A : Set) (B : A → Prop) : Prop where
  _,sp_ : (a : A) → B a → Σsp A B
infixr 4 _,sp_

casesp : ∀{A B}{C : Prop} → ((a : A) → B a → C) → Σsp A B → C
casesp f (a ,sp b) = f a b


_=>_ : Bool → Bool → Bool
_ => true = true
true => false = false
false => false = true