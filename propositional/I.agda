{-# OPTIONS --prop #-}

module I where

   data For : Set
   data Con : Set
   data Sub : Con → Con → Prop
   data Pf  : Con → For → Prop

   data For where
      _⊃_  : For → For → For
      _∧_  : For → For → For
      _∨_ : For → For → For
      ⊤  : For
      ⊥  : For
      
   data Con where
      ◇   : Con
      _▹_   : Con → For → Con
      
   data Sub where
      ε   : ∀{Γ} → Sub Γ ◇
      id  : ∀{Γ} → Sub Γ Γ
      _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      p     : ∀{Γ A} → Sub (Γ ▹ A) Γ
      _,_   : ∀{Γ Δ A} → Sub Δ Γ → Pf Δ A → Sub Δ (Γ ▹ A)

   data Pf where
      _[_]  : ∀{Γ Δ A} → Pf Γ A → Sub Δ Γ → Pf Δ A
      q     : ∀{Γ A} → Pf (Γ ▹ A) A
      ⊃in   : ∀{Γ A B} → Pf (Γ ▹ A) B → Pf Γ (A ⊃ B)
      ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B
      ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
      ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
      ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
      ⊤in   : ∀{Γ} → Pf Γ ⊤
      ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
      ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ A) C → Pf (Γ ▹ B) C → Pf Γ (A ∨ B) → Pf Γ C
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A

   infixl 5 _▹_
   infixl 5 _,_
   infixr 6 _∘_
   infixl 8 _[_]
   infixr 6 _⊃_
   infixr 8 _∧_
   infixr 7 _∨_