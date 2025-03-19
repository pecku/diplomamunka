{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Lib
open import model

module BoolModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

B : Model funar relar
B = record
    { Con = Bool
    ; Sub = {!   !}
    ; _∘_ = {!   !}
    ; ass = {!   !}
    ; id = {!   !}
    ; idl = {!   !}
    ; idr = {!   !}
    ; ◇ = true
    ; ε = {!   !}
    ; ◇η = {!   !}
    ; Tm = {!   !}
    ; _[_]ᵗ = {!   !}
    ; [∘]ᵗ = {!   !}
    ; [id]ᵗ = {!   !}
    ; _▹ₜ = {!   !}
    ; _,ₜ_ = {!   !}
    ; pₜ = {!   !}
    ; qₜ = {!   !}
    ; ▹ₜβ₁ = {!   !}
    ; ▹ₜβ₂ = {!   !}
    ; ▹ₜη = {!   !}
    ; For = {!   !}
    ; _[_]ᶠ = {!   !}
    ; [∘]ᶠ = {!   !}
    ; [id]ᶠ = {!   !}
    ; Pf = {!   !}
    ; _[_]ᵖ = {!   !}
    ; _▹ₚ_ = {!   !}
    ; _,ₚ_ = {!   !}
    ; pₚ = {!   !}
    ; qₚ = {!   !}
    ; ▹ₚβ₁ = {!   !}
    ; ▹ₚη = {!   !}
    ; Rel = {!   !}
    ; Rel[] = {!   !}
    ; fun = {!   !}
    ; fun[] = {!   !}
    ; _⊃_ = {!   !}
    ; ⊃[] = {!   !}
    ; ⊃in = {!   !}
    ; ⊃out = {!   !}
    ; _∧_ = {!   !}
    ; ∧[] = {!   !}
    ; ∧in = {!   !}
    ; ∧out₁ = {!   !}
    ; ∧out₂ = {!   !}
    ; ⊤ = true
    ; ⊤[] = {!   !}
    ; ⊤in = {!   !}
    ; _∨_ = {!   !}
    ; ∨[] = {!   !}
    ; ∨in₁ = {!   !}
    ; ∨in₂ = {!   !}
    ; ∨out = {!   !}
    ; ⊥ = false
    ; ⊥[] = {!   !}
    ; ⊥out = {!   !}
    ; Forall = {!   !}
    ; Forall[] = {!   !}
    ; ∀in = {!   !}
    ; ∀out = {!   !}
    ; ∃ = {!   !}
    ; ∃[] = {!   !}
    ; ∃in = {!   !}
    ; ∃out = {!   !}
    }