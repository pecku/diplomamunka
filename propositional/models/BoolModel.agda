{-# OPTIONS --prop #-}

open import Agda.Builtin.Bool
open import Lib
open import model

-- Bool modell (klasszikus)

module models.BoolModel (PropVar : Set)(propVar : PropVar → Bool) where

    BoolM : Model PropVar
    BoolM = record
       { For = Bool
       ; propVar = propVar
       ; Con = Bool
       ; Sub = λ Γ Δ → (Γ => Δ) ≡ true
       ; Pf = λ Γ A → (Γ => A) ≡ true
       ; ◇ = true
       ; ε = refl
       ; id = λ { {false} → refl
                ; {true} → refl}
       ; _∘_ = λ { {false} {false} {false} → λ _ _ → refl
                   ; {false} {false} {true} → λ _ z → z
                   ; {false} {true} {false} → λ _ _ → refl
                   ; {false} {true} {true} → λ z _ → z
                   ; {true} {false} {false} → λ _ _ → refl
                   ; {true} {false} {true} → λ _ _ → refl
                   ; {true} {true} {false} → λ _ _ → refl
                   ; {true} {true} {true} → λ _ _ → refl}
       ; _[_] = λ { {false} {false} {false} → λ _ _ → refl
                   ; {false} {false} {true} → λ _ _ → refl
                   ; {false} {true} {false} → λ _ z → z
                   ; {false} {true} {true} → λ _ _ → refl
                   ; {true} {false} {false} → λ _ _ → refl
                   ; {true} {false} {true} → λ _ _ → refl
                   ; {true} {true} {false} → λ z _ → z
                   ; {true} {true} {true} → λ _ _ → refl}
       ; _▹_ = _&&_
       ; q = λ { {false} {false} → refl
                ; {false} {true} → refl
                ; {true} {false} → refl
                ; {true} {true} → refl}
       ; p = λ { {false} {false} → refl
                ; {false} {true} → refl
                ; {true} {false} → refl
                ; {true} {true} → refl}
       ; _,_ = λ { {false} {false} {false} → λ _ _ → refl
                   ; {false} {false} {true} → λ _ _ → refl
                   ; {false} {true} {false} → λ _ z → z
                   ; {false} {true} {true} → λ z _ → z
                   ; {true} {false} {false} → λ _ _ → refl
                   ; {true} {false} {true} → λ _ _ → refl
                   ; {true} {true} {false} → λ _ z → z
                   ; {true} {true} {true} → λ _ _ → refl}
       ; _⊃_ = _=>_
       ; ⊃in = λ { {false} {false} {false} _ → refl
                   ; {false} {false} {true} _ → refl
                   ; {false} {true} {false} _ → refl
                   ; {false} {true} {true} _ → refl
                   ; {true} {false} {false} _ → refl
                   ; {true} {false} {true} _ → refl
                   ; {true} {true} {true} _ → refl}
       ; ⊃out = λ { {false} {false} {false} _ _ → refl
                   ; {false} {false} {true} _ _ → refl
                   ; {false} {true} {false} _ _ → refl
                   ; {false} {true} {true} _ _ → refl
                   ; {true} {false} {false} _ p → p
                   ; {true} {false} {true} _ _ → refl
                   ; {true} {true} {true} _ _ → refl}
       ; _∧_ = _&&_
       ; ∧in = λ { {false} {false} {false} _ _ → refl
                   ; {false} {false} {true} _ _ → refl
                   ; {false} {true} {false} _ _ → refl
                   ; {false} {true} {true} _ _ → refl
                   ; {true} {true} {true} _ _ → refl}
       ; ∧out₁ = λ { {false} {false} {false} _ → refl
                   ; {false} {false} {true} _ → refl
                   ; {false} {true} {false} _ → refl
                   ; {false} {true} {true} _ → refl
                   ; {true} {false} {true} p → p
                   ; {true} {true} {false} _ → refl
                   ; {true} {true} {true} _ → refl}
       ; ∧out₂ = λ { {false} {false} {false} _ → refl
                   ; {false} {false} {true} _ → refl
                   ; {false} {true} {false} _ → refl
                   ; {false} {true} {true} _ → refl
                   ; {true} {false} {true} _ → refl
                   ; {true} {true} {false} p → p
                   ; {true} {true} {true} _ → refl}
       ; ⊤ = true
       ; ⊤in = refl
       ; _∨_ = _||_
       ; ∨in₁ = λ { {false} {false} {false} _ → refl
                   ; {false} {false} {true} _ → refl
                   ; {false} {true} {false} _ → refl
                   ; {false} {true} {true} _ → refl
                   ; {true} {true} {false} _ → refl
                   ; {true} {true} {true} _ → refl}
       ; ∨in₂ = λ { {false} {false} {false} _ → refl
                   ; {false} {true} {false} _ → refl
                   ; {false} {false} {true} _ → refl
                   ; {false} {true} {true} _ → refl
                   ; {true} {false} {true} _ → refl
                   ; {true} {true} {true} _ → refl}
       ; ∨out = λ { {false} {false} {false} {false} _ _ _ → refl
                   ; {false} {false} {false} {true} _ _ _ → refl
                   ; {false} {false} {true} {false} _ _ _ → refl
                   ; {false} {false} {true} {true} _ _ _ → refl
                   ; {false} {true} {false} {false} _ _ _ → refl
                   ; {false} {true} {false} {true} _ _ _ → refl
                   ; {false} {true} {true} {false} _ _ _ → refl
                   ; {false} {true} {true} {true} _ _ _ → refl
                   ; {true} {false} {true} {true} _ _ _ → refl
                   ; {true} {true} {false} {true} _ _ _ → refl
                   ; {true} {true} {true} {true} _ _ _ → refl}
       ; ⊥ = false
       ; ⊥out = λ { {false} {false} x → refl
                   ; {false} {true} x → refl}
       }
    
   -- ebben a modellben igaz, hogy minden A : For-ra Pf ◇ (A ∨ ¬ A)
