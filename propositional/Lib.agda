{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool

record 𝟙 : Prop where
   constructor triv

data 𝟘 : Prop where

ind𝟘 : ∀{i}{A : Prop i} → 𝟘 → A
ind𝟘 ()

data _⊎p_ {ℓ}{ℓ'}(A : Prop ℓ)(B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
   ι₁ : A → A ⊎p B
   ι₂ : B → A ⊎p B            

ind⊎p : ∀{i j k}{A : Prop i}{B : Prop j}(C : A ⊎p B → Prop k) →
  ((x : A) → C (ι₁ x)) → ((y : B) → C (ι₂ y)) → (w : A ⊎p B) → C w
ind⊎p C u v (ι₁ x) = u x
ind⊎p C u v (ι₂ y) = v y

infix 2 _×p_
-- data _×p_ {i}(A B : Prop i) : Prop i where
--    _,p_ : A → B → A ×p B
record _×p_ {i}(A B : Prop i) : Prop i where
   constructor _,p_
   field
      proj₁ : A
      proj₂ : B
open _×p_ public

infix 0 _↔_
_↔_ : ∀{i j} → Prop i → Prop j → Prop (i ⊔ j)
A ↔ B = (A → B) ×p (B → A)

fst : {A B : Prop} → A ×p B → A
fst (a ,p b) = a

snd : {A B : Prop} → A ×p B → B
snd (a ,p b) = b

_&&_ : Bool → Bool → Bool
true && true = true
true && false = false
false && true = false
false && false = false

_||_ : Bool → Bool → Bool
true || false = true
true || true = true
false || true = true
false || false = false

_=>_ : Bool → Bool → Bool
_ => true = true
true => false = false
false => false = true

¬ : Bool → Bool
¬ true = false
¬ false = true

¬p_ : ∀{ℓ}(A : Prop ℓ) → Prop ℓ
¬p A = A → 𝟘

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
   instance refl : a ≡ a

⊎pidl : ∀{ℓ}{A : Prop ℓ} → 𝟘 ⊎p A → A
⊎pidl (ι₂ a) = a

⊎comm : ∀{ℓ}{A B : Prop ℓ} → A ⊎p B → B ⊎p A
⊎comm (ι₁ a) = ι₂ a 
⊎comm (ι₂ b) = ι₁ b