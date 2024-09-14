{-# OPTIONS --prop #-}

open import Lib 
open import model
open import models.Tarski

module proofs.TarskiProofs where

    module T = Model Tarski

    open T

    comm : {A B : For} → Pf ◇ (A ∧ B ⊃ B ∧ A)
    comm _ (a ,p b) = b ,p a

    curry : {A B C : For} → Pf ◇ ((A ∧ B ⊃ C) ⊃ A ⊃ B ⊃ C)
    curry _ a∧b⊃c a b = a∧b⊃c (a ,p b)

--   law1 (A ∧ B) ∧ C ⇔ A ∧ (B ∧ C)
--   law2 ⊤ ∧ A ⇔ A
--   law3 A ∧ B ⇔ B ∧ A
--   law4 (A ∨ B) ∨ C ⇔ A ∨ (B ∨ C)
--   law5 ⊥ ∨ A ⇔ A
--   law6 A ∨ B ⇔ B ∨ A
--   law7 (A ∨ B) ∧ C ⇔ A ∧ C ∨ B ∧ C
--   law8 (A ∧ B) ∨ C ⇔ (A ∨ C) ∧ (B ∨ C)
--   law9 ⊤ ⊃ A ⇔ A
--   law10 A ⊃ (B ⊃ C) ⇔ (A ∧ B) ⊃ C
--   law11 (A ∨ B) ⊃ C ⇔ (A ⊃ C) ∧ (B ⊃ C)

    law1 : {A B C : For} → Pf ◇ ((A ∧ B) ∧ C) ↔ Pf ◇ (A ∧ (B ∧ C))
    law1 = (λ x con → fst (fst (x con)) ,p (snd (fst (x con)) ,p snd (x con)))
           ,p
           (λ x con → (fst (x con) ,p fst (snd (x con))) ,p snd (snd (x con)))

    law2 : {A : For} → Pf ◇ (⊤ ∧ A) ↔ Pf ◇ A
    law2 = (λ x con → snd (x con)) ,p λ x con → triv ,p x con

    law3 : {A B : For} → Pf ◇ (A ∧ B) ↔ Pf ◇ (B ∧ A)
    law3 = (λ x con → snd (x con) ,p fst (x con)) ,p (λ x con → snd (x con) ,p fst (x con))

    law4 : {A B C : For} → Pf ◇ ((A ∨ B) ∨ C) ↔ Pf ◇ (A ∨ (B ∨ C))
    proj₁ law4 x con with (x con)
    ... | ι₁ (ι₁ a) = ι₁ a
    ... | ι₁ (ι₂ b) = ι₂ (ι₁ b)
    ... | ι₂ c = ι₂ (ι₂ c)
    proj₂ law4 x con with (x con)
    ... | ι₁ a = ι₁ (ι₁ a)
    ... | ι₂ (ι₁ b) = ι₁ (ι₂ b)
    ... | ι₂ (ι₂ c) = ι₂ c

    law5 : {A : For} → Pf ◇ (⊥ ∨ A) ↔ Pf ◇ A
    law5 = (λ x con → ⊎pidl (x con)) ,p λ x con → ι₂ (x con)

    law6 : {A B : For} → Pf ◇ (A ∨ B) ↔ Pf ◇ (B ∨ A)
    law6 = (λ x con → ⊎comm (x con)) ,p (λ x con → ⊎comm (x con))

    law7 : {A B C : For} → Pf ◇ ((A ∨ B) ∧ C) ↔ Pf ◇ (A ∧ C ∨ B ∧ C)
    proj₁ law7 x con with (x con)
    ... | ι₁ a ,p c = ι₁ (a ,p c)
    ... | ι₂ b ,p c = ι₂ (b ,p c)
    proj₂ law7 x con with (x con)
    ... | ι₁ (a ,p c) = ι₁ a ,p c
    ... | ι₂ (b ,p c) = ι₂ b ,p c

    law8 : {A B C : For} → Pf ◇ ((A ∧ B) ∨ C) ↔ Pf ◇ ((A ∨ C) ∧ (B ∨ C))
    proj₁ law8 x con with (x con)
    ... | ι₁ (a ,p b) = ι₁ a ,p ι₁ b
    ... | ι₂ c = ι₂ c ,p ι₂ c
    proj₂ law8 x con with (x con)
    ... | ι₁ a ,p ι₁ b = ι₁ (a ,p b)
    ... | ι₁ a ,p ι₂ c = ι₂ c
    ... | ι₂ c ,p ι₁ b = ι₂ c
    ... | ι₂ c₁ ,p ι₂ c₂ = ι₂ c₂

    law9 : {A : For} → Pf ◇ (⊤ ⊃ A) ↔ Pf ◇ A
    proj₁ law9 x con = x con con
    proj₂ law9 x con = λ _ → x con

    law10 : {A B C : For} → Pf ◇ (A ⊃ (B ⊃ C)) ↔ Pf ◇ ((A ∧ B) ⊃ C)
    proj₁ law10 x con (a ,p b) = x con a b
    proj₂ law10 x con a b = x con (a ,p b)

    law11 : {A B C : For} → Pf ◇ ((A ∨ B) ⊃ C) ↔ Pf ◇ ((A ⊃ C) ∧ (B ⊃ C))
    proj₁ law11 x con with (x con)
    ... | y = (λ a → y (ι₁ a)) ,p (λ b → y (ι₂ b))
    proj₂ law11 x con (ι₁ a) = proj₁ (x con) a
    proj₂ law11 x con (ι₂ b) = proj₂ (x con) b

--   De Morgan's laws

--   ¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B
    DM1 : {A B : For} → Pf ◇ (¬p (A ∧ B)) ↔ Pf ◇ (¬p A ∨ ¬p B)
    proj₁ DM1 x con  = {!   !}
    proj₂ DM1 x con (a ,p b) with (x con)
    ... | ι₁ a→𝟘 = a→𝟘 a
    ... | ι₂ b→𝟘 = b→𝟘 b
 
--   ¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B
    DM2 : {A B : For} → Pf ◇ (¬p (A ∨ B)) ↔ Pf ◇ (¬p A ∧ ¬p B)
    proj₁ DM2 x con with (x con)
    ... | y = (λ a → y (ι₁ a)) ,p λ b → y (ι₂ b) 
    proj₂ DM2 x con (ι₁ a) = proj₁ (x con) a
    proj₂ DM2 x con (ι₂ b) = proj₂ (x con) b