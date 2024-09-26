{-# OPTIONS --prop #-}

data _≡_ {ℓ}{A : Set ℓ}(a : A) : A → Prop ℓ where
   instance refl : a ≡ a

infix 4 _≡_