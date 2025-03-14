{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib
open import model
open import Syntax

module Iterator
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (M : Model funar relar)
  where

module M = Model M
module S = Syntax funar relar
module I = Model S.I

⟦_⟧Ct : S.Con → M.Con
⟦ ◇ ⟧Ct = M.◇
⟦ Γ ▹ₜ ⟧Ct = ⟦ Γ ⟧Ct M.▹ₜ

⟦_⟧C : I.Con → M.Con

⟦_⟧F : ∀{Γ} → I.For Γ → M.For ⟦ Γ ⟧C

⟦_⟧Cp : ∀{Γ} → S.Conp Γ → M.Con

⟦ Γ , Γₚ ⟧C = ⟦ Γₚ ⟧Cp

⟦_⟧Cp {Γ} ◇ₚ        = ⟦ Γ ⟧Ct
⟦_⟧Cp {Γ} (Γₚ ▹ₚ A) = ⟦ Γₚ ⟧Cp M.▹ₚ ⟦_⟧F {Γ , Γₚ} A



-- ⟦ Γ ▹ₜ , ◇ₚ ⟧C = ⟦ Γ , ◇ₚ ⟧C M.▹ₜ
-- ⟦ Γ ▹ₜ , Γₚ ▹ₚ A ⟧C = {! ⟦ Γ , Γₚ ⟧C M.▹ₜ M.▹ₚ ⟦_⟧F A  !} -- ⟦ Γ , S.restrictConp Γₚ ⟧C M.▹ₜ M.▹ₚ {! ⟦_⟧F A  !} --⟦_⟧F {Γ , S.restrictConp Γₚ} ?
-- ⟦ ◇ , ◇ₚ ⟧C = M.◇
-- ⟦ ◇ , Γₚ ▹ₚ A ⟧C = ⟦ ◇ , Γₚ ⟧C M.▹ₚ (⟦_⟧F {◇ , Γₚ} A)
-- ⟦ Γ ▹ₜ , Γₚ ⟧C = {!  ⟦ Γ , Γₚ ⟧C  !}
-- ⟦ ◇ , ◇ₚ ⟧C = M.◇
-- ⟦ ◇ , Γₚ ▹ₚ A ⟧C = ⟦ ◇ , Γₚ ⟧C M.▹ₚ (⟦_⟧F {◇ , Γₚ} A)
-- ⟦ Γ ▹ₜ , ◇ₚ ⟧C = ⟦ Γ , ◇ₚ ⟧C M.▹ₜ
-- ⟦ Γ ▹ₜ , Γₚ ▹ₚ A ⟧C = {!   !}

-- ⟦_⟧S : ∀{Γ Γₚ Δ Δₚ} → Σ (I.Sub Δ Γ) (λ γ → Lift (I.Subp Δ Δₚ (Γₚ I.[ γ ]Conp))) → M.Sub ⟦ Δ , Δₚ ⟧C ⟦ Γ , Γₚ ⟧C
-- ⟦_⟧S = {!   !}

⟦_⟧T : ∀{Γ} → I.Tm Γ → M.Tm ⟦ Γ ⟧C
⟦_⟧T = {!   !}

⟦_⟧F {Γ} (A ⊃ B)     = M._⊃_  (⟦_⟧F {Γ} A) (⟦_⟧F {Γ} B)
⟦_⟧F {Γ} (A ∧ B)     = M._∧_ (⟦_⟧F {Γ} A) (⟦_⟧F {Γ} B)
⟦_⟧F {Γ} ⊤           = M.⊤ 
⟦_⟧F {Γ} (A ∨ B)     = M._∨_ (⟦_⟧F {Γ} A) (⟦_⟧F {Γ} B)
⟦_⟧F {Γ} ⊥           = M.⊥
⟦_⟧F {Γ} (Forall A) = M.Forall (⟦_⟧F {((fst Γ ▹ₜ) , S._[_]Conp (snd Γ) S.pₜ)} A)                         --{!M.Forall (⟦_⟧F {Γ} A)!}
⟦_⟧F {Γ} (∃ A)       = {!   !} -- M.∃ (⟦_⟧F {Γ} A)
⟦_⟧F {Γ} (Rel ar ts) = {!   !} --M.Rel ar ((map ⟦_⟧T ts))


-- ⟦_⟧P : ∀{Γ A} → I.Pf (fst Γ) (snd Γ) A → M.Pf ⟦ Γ ⟧C (⟦_⟧F {Γ} A)
-- ⟦_⟧P = {!   !}          