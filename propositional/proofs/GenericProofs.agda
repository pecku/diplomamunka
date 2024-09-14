{-# OPTIONS --prop #-}

open import Lib hiding (¬)
open import model

module proofs.GenericProofs {i} {j} (M : Model {i} {j}) where

open Model M

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
proj₁ law1 pf = ∧in (∧out₁ (∧out₁ pf)) (∧in (∧out₂ (∧out₁ pf)) (∧out₂ pf))
proj₂ law1 pf = ∧in (∧in (∧out₁ pf) (∧out₁ (∧out₂ pf))) (∧out₂ (∧out₂ pf))

law2 : {A : For} → Pf ◇ (⊤ ∧ A) ↔ Pf ◇ A
proj₁ law2 = ∧out₂
proj₂ law2 = ∧in ⊤in

law3 : {A B : For} → Pf ◇ (A ∧ B) ↔ Pf ◇ (B ∧ A)
proj₁ law3 pf = ∧in (∧out₂ pf) (∧out₁ pf)
proj₂ law3 pf = ∧in (∧out₂ pf) (∧out₁ pf)

law4 : {A B C : For} → Pf ◇ ((A ∨ B) ∨ C) ↔ Pf ◇ (A ∨ (B ∨ C))
proj₁ law4 pf = ∨out (∨out (∨in₁ q) (∨in₂ (∨in₁ q)) q) (∨in₂ (∨in₂ q)) pf
proj₂ law4 pf = ∨out (∨in₁ (∨in₁ q)) (∨out (∨in₁ (∨in₂ q)) (∨in₂ q) q) pf

law5 : {A : For} → Pf ◇ (⊥ ∨ A) ↔ Pf ◇ A
proj₁ law5 = ∨out (⊥out q) q
proj₂ law5 = ∨in₂

law6 : {A B : For} → Pf ◇ (A ∨ B) ↔ Pf ◇ (B ∨ A)
proj₁ law6 pf = ∨out (∨in₂ q) (∨in₁ q) pf
proj₂ law6 pf = ∨out (∨in₂ q) (∨in₁ q) pf

law7 : {A B C : For} → Pf ◇ ((A ∨ B) ∧ C) ↔ Pf ◇ (A ∧ C ∨ B ∧ C)
proj₁ law7 pf = ∨out (∨in₁ (∧in q (∧out₂ pf [ p ]))) (∨in₂ (∧in q (∧out₂ pf [ p ]))) (∧out₁ pf)
proj₂ law7 pf = ∧in (∨out (∨in₁ (∧out₁ q)) (∨in₂ (∧out₁ q)) pf) (∨out (∧out₂ q) (∧out₂ q) pf)

-- law8 : {A B C : For} → Pf ◇ ((A ∧ B) ∨ C) ↔ Pf ◇ ((A ∨ C) ∧ (B ∨ C))
-- proj₁ law8 pf = ∧in (∨out (∨in₁ (∧out₁ q)) (∨in₂ q) pf) (∨out (∨in₁ (∧out₂ q)) (∨in₂ q) pf)
-- proj₂ law8 pf = ∨out ({!   !}) (∨in₂ q) (∧out₁ pf)

law9 : {A : For} → Pf ◇ (⊤ ⊃ A) ↔ Pf ◇ A
proj₁ law9 pf = ⊃out pf ⊤in
proj₂ law9 pf = ⊃in (pf [ ε ])

asd : {Γ : Con} {A B : For} → Pf Γ (A ⊃ B) → Pf (Γ ▹ A) B
asd pf = ⊃out (pf [ p ]) q

law10 : {A B C : For} → Pf ◇ (A ⊃ (B ⊃ C)) ↔ Pf ◇ ((A ∧ B) ⊃ C)
proj₁ law10 pf = ⊃in ((⊃out (⊃out (pf [ ε ]) (∧out₁ q)) (∧out₂ q)))
proj₂ law10 pf = ⊃in (⊃in (⊃out (pf [ ε ]) (∧in (q [ p ]) q)))

-- law11 : {A B C : For} → Pf ◇ ((A ∨ B) ⊃ C) ↔ Pf ◇ ((A ⊃ C) ∧ (B ⊃ C))
-- proj₁ law11 pf = ∧in (⊃in (⊃out (pf [ ε ]) (∨in₁ q))) {!   !}
-- proj₂ law11 pf = {!   !}



¬ : For → For
¬ A = A ⊃ ⊥

--   De Morgan's laws

-- --   ¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B
-- DM1 : {A B C : For} → Pf ◇ (¬ (A ∧ B)) ↔ Pf ◇ (¬ A ∨ ¬ B)
-- proj₁ DM1 pf = {!   !}
-- proj₂ DM1 pf = {!   !}

-- --   ¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B
-- DM2 : {A B C : For} → Pf ◇ (¬ (A ∨ B)) ↔ Pf ◇ (¬ A ∧ ¬ B)
-- proj₁ DM2 pf = {!   !}
-- proj₂ DM2 pf = {!   !} 