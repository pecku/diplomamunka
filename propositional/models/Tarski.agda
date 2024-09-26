{-# OPTIONS --prop #-}

open import Lib

-- Tarski modell

module models.Tarski (PropVar : Set)(propVar : PropVar → Prop) where

open import model PropVar

Tarski : Model
Tarski = record
   { For = Prop
   ; propVar = propVar
   ; Con = Prop
   ; Sub = λ Δ Γ → Δ → Γ
   ; Pf = λ Γ A → Γ → A
   ; ◇ = 𝟙
   ; ε = λ _ → triv
   ; id = λ x → x
   ; _∘_ = λ Δ→Γ θ→Δ θ → Δ→Γ (θ→Δ θ)
   ; _[_] = λ Γ→A Δ→Γ Δ → Γ→A (Δ→Γ Δ)
   ; _▹_ = _×p_
   ; q = λ { (_ ,p a) → a }
   ; p = λ { (g ,p _) → g }
   ; _,_ = λ Δ→Γ Δ→A Δ → Δ→Γ Δ ,p Δ→A Δ
   ; _⊃_ = λ A B → A → B
   ; ⊃in = λ Γ×pA→B Γ A → Γ×pA→B (Γ ,p A)
   ; ⊃out = λ Γ→A→B Γ→A Γ → Γ→A→B Γ (Γ→A Γ)
   ; _∧_ = _×p_
   ; ∧in = λ Γ→A Γ→B Γ → Γ→A Γ ,p Γ→B Γ
   ; ∧out₁ = λ Γ→A×pB Γ → fst (Γ→A×pB Γ)
   ; ∧out₂ = λ Γ→A×pB Γ → snd (Γ→A×pB Γ)
   ; ⊤ = 𝟙
   ; ⊤in = λ _ → triv
   ; _∨_ = _⊎p_
   ; ∨in₁ = λ Γ→A Γ → ι₁ (Γ→A Γ)
   ; ∨in₂ = λ Γ→B Γ → ι₂ (Γ→B Γ)
   ; ∨out = λ Γ×pA→C Γ×pB→C Γ→A⊎pB Γ → ind⊎p _ (λ α → Γ×pA→C (Γ ,p α)) (λ α → Γ×pB→C (Γ ,p α)) (Γ→A⊎pB Γ)
   ; ⊥ = 𝟘
   ; ⊥out = λ Γ→𝟘 Γ → ind𝟘 (Γ→𝟘 Γ)
   }
