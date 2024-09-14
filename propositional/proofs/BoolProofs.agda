{-# OPTIONS --prop #-}

open import Agda.Builtin.Bool
open import Lib
open import model
open import models.BoolModel

module proofs.BoolProofs where

   module B = Model BoolM

   open B

   lem : (A : For) → Pf ◇ (A ∨ ¬ A)
   lem false = refl
   lem true = refl

   comm : (A B : For) → Pf ◇ (A ∧ B ⊃ B ∧ A)
   comm false false = refl
   comm false true = refl
   comm true false = refl
   comm true true = refl


-- (A x B -> C) -> A -> B -> C

   curry : (A B C : For) → Pf ◇ ((A ∧ B ⊃ C) ⊃ A ⊃ B ⊃ C)
   curry false false false = refl
   curry false false true  = refl
   curry false true  false = refl
   curry false true  true  = refl
   curry true  false false = refl
   curry true  false true  = refl
   curry true  true  false = refl
   curry true  true  true  = refl

--   pf1:
--   A1: Ha Aladár busszal utazik, és a busz késik, akkor nem ér oda a találkozóra.
--      B ∧ K → ¬T
--   A2: Ha nem ér oda a találkozóra és nem tud telefonálni, akkor nem kapja meg az
--   állást.
--      ¬T ∧ ¬P → ¬A
--   A3: Ha rossz a kocsija, akkor busszal kell mennie.
--      C → B
--   A4: Aladárnak rossz napja van, mert a kocsija nem indul, rossz a telefonja és a busz
--   késik.
--      (C ∧ ¬P ∧ K) → N
--   B: Tehát Aladár nem kapja meg az állást.
--      ¬A
   pf1 : {B K T P A C N : For} →
         Pf (◇ ▹
               (B ∧ K ⊃ B ∧ ¬ T) ▹
               (¬ T ∧ ¬ P ⊃ ¬ A) ▹
               (C ⊃ B) ▹
               (C ∧ ¬ P ∧ K ⊃ N)
               )
         (¬ A)
   pf1 = {!   !}

--   pf2
--   A1: Ha elmegyünk Pécsre, akkor Hévı́zre és Keszthelyre is.
--   A2: Ha nem megyünk Keszthelyre, akkor elmegyünk Hévı́zre.
--   A3: Ha elmegyünk Keszthelyre, akkor Pécsre is. 
--   B: Tehát elmegyünk Hévı́zre.


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


   -- law1_g : {A B C : For} → Pf ◇ ((A ∧ B) ∧ C) ↔ Pf ◇ (A ∧ (B ∧ C))
   -- law1_g = (λ pf → ∧in (∧out₁ (∧out₁ pf)) (∧in (∧out₂ (∧out₁ pf)) (∧out₂ pf)))
   --          ,p
   --          (λ pf → ∧in (∧in (∧out₁ pf) (∧out₁ (∧out₂ pf))) (∧out₂ (∧out₂ pf)))

   law1 : (A B C : For) → Pf ◇ ((A ∧ B) ∧ C) ↔ Pf ◇ (A ∧ (B ∧ C))
   law1 false false false = (λ x → x)    ,p (λ x → x)
   law1 false false true  = (λ x → x)    ,p (λ x → x)
   law1 false true  false = (λ x → x)    ,p (λ x → x)
   law1 false true  true  = (λ x → x)    ,p (λ x → x)
   law1 true  false false = (λ x → x)    ,p (λ x → x)
   law1 true  false true  = (λ x → x)    ,p (λ x → x)
   law1 true  true  false = (λ x → x)    ,p (λ x → x)
   law1 true  true  true  = (λ _ → refl) ,p (λ _ → refl)

   open import proofs.GenericProofs BoolM using () renaming (law1 to law1_g)

   law1' : {A B C : For} → Pf ◇ ((A ∧ B) ∧ C) ↔ Pf ◇ (A ∧ (B ∧ C))
   law1' = law1_g


   law2 : (A : For) → Pf ◇ (⊤ ∧ A) ↔ Pf ◇ A
   law2 false = (λ x → x)    ,p (λ x → x)
   law2 true  = (λ _ → refl) ,p (λ _ → refl)

   law3 : (A B : For) → Pf ◇ (A ∧ B) ↔ Pf ◇ (B ∧ A)
   law3 false false = (λ x → x)    ,p (λ x → x)
   law3 false true  = (λ x → x)    ,p (λ x → x)
   law3 true  false = (λ x → x)    ,p (λ x → x)
   law3 true  true  = (λ _ → refl) ,p (λ x → refl)

   law4 : (A B C : For) → Pf ◇ ((A ∨ B) ∨ C) ↔ Pf ◇ (A ∨ (B ∨ C))
   law4 false false false = (λ x → x)    ,p (λ x → x)
   law4 false false true  = (λ _ → refl) ,p (λ _ → refl)
   law4 false true  false = (λ _ → refl) ,p (λ _ → refl)
   law4 false true  true  = (λ _ → refl) ,p (λ _ → refl)
   law4 true  false false = (λ _ → refl) ,p (λ _ → refl)
   law4 true  false true  = (λ _ → refl) ,p (λ _ → refl)
   law4 true  true  false = (λ _ → refl) ,p (λ _ → refl)
   law4 true  true  true  = (λ _ → refl) ,p (λ _ → refl)

   law5 : (A : For) → Pf ◇ (⊥ ∨ A) ↔ Pf ◇ A
   law5 false = (λ x → x)    ,p (λ x → x)
   law5 true  = (λ _ → refl) ,p (λ _ → refl)

   law6 : (A B : For) → Pf ◇ (A ∨ B) ↔ Pf ◇ (B ∨ A)
   law6 false false = (λ x → x)    ,p (λ x → x)
   law6 false true  = (λ _ → refl) ,p (λ _ → refl)
   law6 true  false = (λ _ → refl) ,p (λ _ → refl)
   law6 true  true  = (λ _ → refl) ,p (λ _ → refl)

   law7 : (A B C : For) → Pf ◇ ((A ∨ B) ∧ C) ↔ Pf ◇ (A ∧ C ∨ B ∧ C)
   law7 false false false = (λ x → x)    ,p (λ x → x)
   law7 false false true  = (λ x → x)    ,p (λ x → x)
   law7 false true  false = (λ x → x)    ,p (λ x → x)
   law7 false true  true  = (λ x → refl) ,p (λ x → refl)
   law7 true  false false = (λ x → x)    ,p (λ x → x)
   law7 true  false true  = (λ x → refl) ,p (λ x → refl)
   law7 true  true  false = (λ x → x)    ,p (λ x → x)
   law7 true  true  true  = (λ x → refl) ,p (λ x → refl)

   law8 : (A B C : For) → Pf ◇ ((A ∧ B) ∨ C) ↔ Pf ◇ ((A ∨ C) ∧ (B ∨ C))
   law8 false false false = (λ x → x)    ,p (λ x → x)
   law8 false false true  = (λ _ → refl) ,p (λ _ → refl)
   law8 false true  false = (λ x → x)    ,p (λ x → x)
   law8 false true  true  = (λ _ → refl) ,p (λ _ → refl)
   law8 true  false false = (λ x → x)    ,p (λ x → x)
   law8 true  false true  = (λ _ → refl) ,p (λ _ → refl)
   law8 true  true  false = (λ _ → refl) ,p (λ _ → refl)
   law8 true  true  true  = (λ _ → refl) ,p (λ _ → refl)

   law9 : (A : For) → Pf ◇ (⊤ ⊃ A) ↔ Pf ◇ A
   law9 false = (λ x → x)    ,p (λ x → x)
   law9 true  = (λ _ → refl) ,p (λ _ → refl)

   law10 : (A B C : For) → Pf ◇ (A ⊃ (B ⊃ C)) ↔ Pf ◇ ((A ∧ B) ⊃ C)
   law10 false false false = (λ _ → refl) ,p (λ _ → refl)
   law10 false false true  = (λ _ → refl) ,p (λ _ → refl)
   law10 false true  false = (λ _ → refl) ,p (λ _ → refl)
   law10 false true  true  = (λ _ → refl) ,p (λ _ → refl)
   law10 true  false false = (λ _ → refl) ,p (λ _ → refl)
   law10 true  false true  = (λ _ → refl) ,p (λ _ → refl)
   law10 true  true  false = (λ x → x)    ,p (λ x → x)
   law10 true  true  true  = (λ _ → refl) ,p (λ _ → refl)

   law11 : (A B C : For) → Pf ◇ ((A ∨ B) ⊃ C) ↔ Pf ◇ ((A ⊃ C) ∧ (B ⊃ C))
   law11 false false false = (λ _ → refl) ,p (λ _ → refl)
   law11 false false true  = (λ _ → refl) ,p (λ _ → refl)
   law11 false true  false = (λ x → x)    ,p (λ x → x)
   law11 false true  true  = (λ _ → refl) ,p (λ _ → refl)
   law11 true  false false = (λ x → x)    ,p (λ x → x)
   law11 true  false true  = (λ _ → refl) ,p (λ _ → refl)
   law11 true  true  false = (λ x → x)    ,p (λ x → x)
   law11 true  true  true  = (λ _ → refl) ,p (λ _ → refl)

--   De Morgan's laws

--   ¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B
   DM1 : (A B C : For) → Pf ◇ (¬ (A ∧ B)) ↔ Pf ◇ (¬ A ∨ ¬ B)
   DM1 false false false = (λ _ → refl) ,p (λ _ → refl)
   DM1 false false true  = (λ _ → refl) ,p (λ _ → refl)
   DM1 false true  false = (λ _ → refl) ,p (λ _ → refl)
   DM1 false true  true  = (λ _ → refl) ,p (λ _ → refl)
   DM1 true  false false = (λ _ → refl) ,p (λ _ → refl)
   DM1 true  false true  = (λ _ → refl) ,p (λ _ → refl)
   DM1 true  true  false = (λ x → x)    ,p (λ x → x)
   DM1 true  true  true  = (λ x → x)    ,p (λ x → x)

--   ¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B
   DM2 : (A B C : For) → Pf ◇ (¬ (A ∨ B)) ↔ Pf ◇ (¬ A ∧ ¬ B)
   DM2 false false false = (λ _ → refl) ,p (λ _ → refl)
   DM2 false false true  = (λ _ → refl) ,p (λ _ → refl)
   DM2 false true  false = (λ x → x)    ,p (λ x → x)
   DM2 false true  true  = (λ x → x)    ,p (λ x → x)
   DM2 true  false false = (λ x → x)    ,p (λ x → x)
   DM2 true  false true  = (λ x → x)    ,p (λ x → x)
   DM2 true  true  false = (λ x → x)    ,p (λ x → x) 
   DM2 true  true  true  = (λ x → x)    ,p (λ x → x) 