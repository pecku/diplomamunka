{-# OPTIONS --prop #-}

open import Agda.Primitive

module model (PropVar : Set) where

import I PropVar as I

record Model {i j} : Set (lsuc i ⊔ lsuc j) where
   field
      For : Set i
      Con : Set i
      Sub : Con → Con → Prop j
      Pf  : Con → For → Prop j

      propVar : PropVar → For

      ◇   : Con
      ε   : ∀{Γ} → Sub Γ ◇
      id  : ∀{Γ} → Sub Γ Γ
      _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      _[_]  : ∀{Γ Δ A} → Pf Γ A → Sub Δ Γ → Pf Δ A
      _▹_   : Con → For → Con
      q     : ∀{Γ A} → Pf (Γ ▹ A) A
      p     : ∀{Γ A} → Sub (Γ ▹ A) Γ
      _,_   : ∀{Γ Δ A} → Sub Δ Γ → Pf Δ A → Sub Δ (Γ ▹ A)

      _⊃_   : For → For → For
      ⊃in   : ∀{Γ A B} → Pf (Γ ▹ A) B → Pf Γ (A ⊃ B)
      ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B

      _∧_   : For → For → For
      ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
      ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
      ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B

      ⊤     : For
      ⊤in   : ∀{Γ} → Pf Γ ⊤

      _∨_   : For → For → For
      ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
      ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ A) C → Pf (Γ ▹ B) C → Pf Γ (A ∨ B) → Pf Γ C

      ⊥     : For
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A
   
   infixl 5 _▹_
   infixl 5 _,_
   infixr 6 _∘_
   infixl 8 _[_]
   infixr 6 _⊃_
   infixr 8 _∧_
   infixr 7 _∨_

   ⟦_⟧F : I.For → For
   ⟦_⟧C : I.Con → Con
   ⟦_⟧S : {C₁ C₂ : I.Con} → I.Sub C₁ C₂ → Sub ⟦ C₁ ⟧C ⟦ C₂ ⟧C
   ⟦_⟧P : {C : I.Con}{F : I.For} → I.Pf C F → Pf ⟦ C ⟧C ⟦ F ⟧F

   ⟦ I.propVar X ⟧F = propVar X
   ⟦ f₁ I.⊃ f₂ ⟧F = ⟦ f₁ ⟧F ⊃ ⟦ f₂ ⟧F
   ⟦ f₁ I.∧ f₂ ⟧F = ⟦ f₁ ⟧F ∧ ⟦ f₂ ⟧F
   ⟦ f₁ I.∨ f₂ ⟧F = ⟦ f₁ ⟧F ∨ ⟦ f₂ ⟧F
   ⟦ I.⊤ ⟧F = ⊤
   ⟦ I.⊥ ⟧F = ⊥

   ⟦ I.◇     ⟧C = ◇
   ⟦ c I.▹ f ⟧C = ⟦ c ⟧C ▹ ⟦ f ⟧F

   ⟦ I.ε       ⟧S = ε
   ⟦ I.id      ⟧S = id
   ⟦ s₁ I.∘ s₂ ⟧S = ⟦ s₁ ⟧S ∘ ⟦ s₂ ⟧S
   ⟦ I.p       ⟧S = p
   ⟦ s I., p   ⟧S = ⟦ s ⟧S , ⟦ p ⟧P

   ⟦ p I.[ s ]        ⟧P = ⟦ p ⟧P [ ⟦ s ⟧S ]
   ⟦ I.q              ⟧P = q
   ⟦ I.⊃in p          ⟧P = ⊃in ⟦ p ⟧P
   ⟦ I.⊃out p₁ p₂     ⟧P = ⊃out ⟦ p₁ ⟧P ⟦ p₂ ⟧P
   ⟦ I.∧in p₁ p₂      ⟧P = ∧in ⟦ p₁ ⟧P ⟦ p₂ ⟧P
   ⟦ I.∧out₁ p        ⟧P = ∧out₁ ⟦ p ⟧P
   ⟦ I.∧out₂ p        ⟧P = ∧out₂ ⟦ p ⟧P
   ⟦ I.⊤in            ⟧P = ⊤in
   ⟦ I.∨in₁ p         ⟧P = ∨in₁ ⟦ p ⟧P
   ⟦ I.∨in₂ p         ⟧P = ∨in₂ ⟦ p ⟧P
   ⟦ I.∨out p₁ p₂ p₃  ⟧P = ∨out ⟦ p₁ ⟧P ⟦ p₂ ⟧P ⟦ p₃ ⟧P
   ⟦ I.⊥out p         ⟧P = ⊥out ⟦ p ⟧P


   -- ¬ A := A ⊃ ⊥

-- I : Model
-- I = record
--    { For = For
--    ; Con = Con
--    ; Sub = Sub
--    ; Pf = Pf
--    ; ◇ = ◇
--    ; ε = ε
--    ; id = id
--    ; _∘_ = _∘_
--    ; _[_] = _[_]
--    ; _▹_ = _▹_
--    ; q = q
--    ; p = p
--    ; _,_ = _,_
--    ; _⊃_ = _⊃_
--    ; ⊃in = ⊃in
--    ; ⊃out = ⊃out
--    ; _∧_ = _∧_
--    ; ∧in = ∧in
--    ; ∧out₁ = ∧out₁
--    ; ∧out₂ = ∧out₂
--    ; ⊤ = ⊤
--    ; ⊤in = ⊤in
--    ; _∨_ = _∨_
--    ; ∨in₁ = ∨in₁
--    ; ∨in₂ = ∨in₂
--    ; ∨out = ∨out
--    ; ⊥ = ⊥
--    ; ⊥out = ⊥out
--    }
   
-- M.⟦_⟧F : I.For → M.For
-- M.⟦_⟧Pf : I.Pf Γ A → M.Pf ⟦ Γ ⟧Con ⟦ A ⟧For
