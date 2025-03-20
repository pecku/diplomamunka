{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib
open import model
open import Syntax

module Iterator
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  {i}{j}{k}{l}
  (M : Model funar relar {i}{j}{k}{l})
  where

module M = Model M
module S = Syntax funar relar
module I = Model S.I

⟦_⟧Ct : S.Con → M.Con
⟦ ◇ ⟧Ct = M.◇
⟦ Γ ▹ₜ ⟧Ct = ⟦ Γ ⟧Ct M.▹ₜ

⟦_⟧C : I.Con → M.Con

⟦_⟧F' : ∀{Γₜ} → S.For Γₜ → M.For ⟦ Γₜ ⟧Ct

⟦_⟧Cp : ∀{Γ} → S.Conp Γ → M.Con

⟦ Γ , Γₚ ⟧C = ⟦ Γₚ ⟧Cp

⟦p⟧ : ∀{Γₜ}{Γₚ : S.Conp Γₜ} → M.Sub ⟦ Γₚ ⟧Cp ⟦ Γₜ ⟧Ct

⟦_⟧Cp {Γₜ} ◇ₚ        = ⟦ Γₜ ⟧Ct
⟦_⟧Cp {Γₜ} (Γₚ ▹ₚ A) = ⟦ Γₚ ⟧Cp M.▹ₚ ⟦ A ⟧F' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᶠ

⟦p⟧ {Γₜ} {◇ₚ} = M.id
⟦p⟧ {Γₜ} {Γₚ ▹ₚ A} = ⟦p⟧ {Γₜ} {Γₚ} M.∘ M.pₚ

⟦_⟧T' : ∀{Γₜ} → S.Tm Γₜ → M.Tm ⟦ Γₜ ⟧Ct
⟦_⟧Ts' : ∀{n Γₜ} → S.Tm Γₜ ^ n → M.Tm ⟦ Γₜ ⟧Ct ^ n
⟦ var vz ⟧T' = M.qₜ
⟦ var (vs x) ⟧T' = ⟦ var x ⟧T' M.[ M.pₜ ]ᵗ
⟦ fun ar ts ⟧T' = M.fun ar ⟦ ts ⟧Ts'

⟦_⟧Ts' {zero} ts = _
⟦_⟧Ts' {suc n} (t , ts) = ⟦ t ⟧T' , ⟦ ts ⟧Ts'

⟦ A ⊃ B ⟧F' = ⟦ A ⟧F' M.⊃ ⟦ B ⟧F'
⟦ A ∧ B ⟧F' = ⟦ A ⟧F' M.∧ ⟦ B ⟧F'
⟦ ⊤ ⟧F' = M.⊤
⟦ A ∨ B ⟧F' = ⟦ A ⟧F' M.∨ ⟦ B ⟧F'
⟦ ⊥ ⟧F' = M.⊥
⟦ Forall A ⟧F' = M.Forall ⟦ A ⟧F'
⟦ ∃ A ⟧F' = M.∃ ⟦ A ⟧F'
⟦ Rel ar ts ⟧F' = M.Rel ar ⟦ ts ⟧Ts'

⟦_⟧F : ∀{Γ} → I.For Γ → M.For ⟦ Γ ⟧C
⟦_⟧F {Γₜ , Γₚ} A = ⟦ A ⟧F' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᶠ

⟦_⟧T : ∀{Γ} → I.Tm Γ → M.Tm ⟦ Γ ⟧C
⟦_⟧T {Γₜ , Γₚ} t = ⟦ t ⟧T' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᵗ

-- ⟦_⟧S : ∀{Γ Γₚ Δ Δₚ} → Σ (I.Sub Δ Γ) (λ γ → Lift (I.Subp Δ Δₚ (Γₚ I.[ γ ]Conp))) → M.Sub ⟦ Δ , Δₚ ⟧C ⟦ Γ , Γₚ ⟧C
-- ⟦_⟧S = {!   !}

⟦p'⟧ : ∀{Γₜ}{Γₚ : S.Conp Γₜ} → M.Sub (⟦ Γₚ ⟧Cp M.▹ₜ) ⟦ Γₚ S.[ S.pₜ ]Conp ⟧Cp
⟦p'⟧ {Γₜ}{◇ₚ} = M.id
⟦p'⟧ {Γₜ}{Γₚ ▹ₚ A} = ⟦p'⟧ {Γₜ}{Γₚ} M.∘ (M.pₚ M.∘ M.pₜ M.,ₜ M.qₜ) M.,ₚ substP (M.Pf _) {!!} (M.qₚ M.[ M.pₜ ]ᵖ)


⟦_⟧P : ∀{Γ A} → I.Pf Γ A → M.Pf ⟦ Γ ⟧C (⟦_⟧F {Γ} A)
⟦ a [ γ ]ᵖ ⟧P = {!!}
⟦ a [ γₚ ]ᵖᵖ ⟧P = {!!}
⟦ qₚ ⟧P = substP (M.Pf _) (M.[∘]ᶠ ⁻¹) M.qₚ
⟦ ⊃in b ⟧P = substP (M.Pf _) (M.⊃[] ⁻¹) (M.⊃in (substP (M.Pf _) M.[∘]ᶠ ⟦ b ⟧P))
⟦ ⊃out f a ⟧P = M.⊃out (substP (M.Pf _) M.⊃[] ⟦ f ⟧P) ⟦ a ⟧P
⟦ ∧in a b ⟧P = substP (M.Pf _) (M.∧[] ⁻¹) (M.∧in ⟦ a ⟧P ⟦ b ⟧P)
⟦ ∧out₁ a ⟧P = M.∧out₁ (substP (M.Pf _) M.∧[] ⟦ a ⟧P)
⟦ ∧out₂ b ⟧P = M.∧out₂ (substP (M.Pf _) M.∧[] ⟦ b ⟧P)
⟦ ⊤in ⟧P = substP (M.Pf _) (M.⊤[] ⁻¹) M.⊤in
⟦ ∨in₁ a ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₁ ⟦ a ⟧P)
⟦ ∨in₂ b ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₂ ⟦ b ⟧P)
⟦ ∨out ac bc ab ⟧P = M.∨out (substP (M.Pf _) M.[∘]ᶠ ⟦ ac ⟧P) (substP (M.Pf _) M.[∘]ᶠ ⟦ bc ⟧P) (substP (M.Pf _) M.∨[] ⟦ ab ⟧P)
⟦ ⊥out p ⟧P = M.⊥out (substP (M.Pf _) M.⊥[] ⟦ p ⟧P)
⟦_⟧P {Γₜ , Γₚ}{S.Forall A} (∀in a) = substP (M.Pf _) (M.Forall[] ⁻¹) (M.∀in (substP (M.Pf _) (M.[∘]ᶠ ⁻¹ ◾ cong (λ z → ⟦ A ⟧F' M.[ z ]ᶠ) {!!}) (⟦ a ⟧P M.[ ⟦p'⟧ {Γₜ}{Γₚ} ]ᵖ)))
⟦ ∀out p ⟧P = {!!}
⟦ ∃in t p ⟧P = {!!}
⟦ ∃out p p₁ ⟧P = {!!}
