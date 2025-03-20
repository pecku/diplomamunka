{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib
open import model

module Family
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (I : Set)
  (D : I → Set)
  (fun : (n : ℕ) → funar n → (i : I) → D i ^ n → D i)
  (Rel : (n : ℕ) → relar n → (i : I) → D i ^ n → Prop)
  where

$i : {Γ : I → Set}{n : ℕ} → (i : I) → ((i : I) → Γ i → D i) ^ n → Γ i → D i ^ n
$i i ds γ = map (λ x → x i γ) ds

F : Model funar relar
F = record
  { Con = I → Set
  ; Sub = λ Δ Γ → (i : I) → Δ i → Γ i
  ; _∘_ = λ γ δ i Θ → γ i (δ i Θ)
  ; ass = refl
  ; id = λ i γ → γ
  ; idl = refl
  ; idr = refl
  ; ◇ = λ i → 𝟙
  ; ε = _
  ; ◇η = refl
  ; Tm = λ Γ → (i : I) → Γ i → D i
  ; _[_]ᵗ = λ t γ i Δ → t i (γ i Δ)
  ; [∘]ᵗ = refl
  ; [id]ᵗ = refl
  ; _▹ₜ = λ Γ i → Γ i × D i
  ; _,ₜ_ = λ γ t i Δ → γ i Δ , t i Δ
  ; pₜ = λ i → fst
  ; qₜ = λ i → snd
  ; ▹ₜβ₁ = refl
  ; ▹ₜβ₂ = refl
  ; ▹ₜη = refl
  ; For = λ Γ → (i : I) → Γ i → Prop
  ; _[_]ᶠ = λ A γ i Δ → A i (γ i Δ)
  ; [∘]ᶠ = refl
  ; [id]ᶠ = refl
  ; Pf = λ Γ A → (i : I) → (γ : Γ i) → A i γ
  ; _[_]ᵖ = λ a γ i Δ → a i (γ i Δ)
  ; _▹ₚ_ = λ Γ A i → Σ (Γ i) λ γ → Lift (A i γ)
  ; _,ₚ_ = λ γ a i Δ → γ i Δ , mk (a i Δ)
  ; pₚ = λ i → fst
  ; qₚ = λ i a → un (snd a)
  ; ▹ₚβ₁ = refl
  ; ▹ₚη = refl
  ; Rel = λ ar ds i γ → Rel _ ar i ($i i ds γ)
  ; Rel[] = funext λ i → funext λ δ → cong (Rel _ _ _) map∘
  ; fun = λ ar ds i γ → fun _ ar i ($i i ds γ)
  ; fun[] = funext λ i → funext λ δ → cong (fun _ _ _) map∘
  ; _⊃_ = λ A B i γ → (A i γ) → (B i γ)
  ; ⊃[] = refl
  ; ⊃in = λ b i γ a → b i (γ , mk a)
  ; ⊃out = λ f a i γ → f i γ (a i γ)
  ; _∧_ = λ A B i γ → (A i γ) ×p (B i γ)
  ; ∧[] = refl
  ; ∧in = λ a b i γ → a i γ ,p b i γ
  ; ∧out₁ = λ ab i γ → fst (ab i γ)
  ; ∧out₂ = λ ab i γ → snd (ab i γ)
  ; ⊤ = λ _ _ → 𝟙p
  ; ⊤[] = refl
  ; ⊤in = λ _ _ → tt
  ; _∨_ = λ A B i γ → (A i γ) ⊎p (B i γ)
  ; ∨[] = refl
  ; ∨in₁ = λ a i γ → inl (a i γ)
  ; ∨in₂ = λ b i γ → inr (b i γ)
  ; ∨out = λ ac bc ab i γ → casep (λ a → ac i (γ , mk a)) (λ b → bc i (γ , mk b)) (ab i γ)
  ; ⊥ = λ _ _ → 𝟘p
  ; ⊥[] = refl
  ; ⊥out = λ b i γ → exfalsop (b i γ)
  ; Forall = λ A i γ → (d : D i) → A i (γ , d)
  ; Forall[] = refl
  ; ∀in = λ a i γ d → a i (γ , d)
  ; ∀out = λ a i γd → a i (fst γd) (snd γd)
  ; ∃ = λ A i γ → Σsp (D i) λ d → A i (γ , d)
  ; ∃[] = refl
  ; ∃in = λ d a i γ → d i γ ,sp a i γ
  ; ∃out = λ f da i γ → casesp (λ d a → f i ((γ , d) , mk a)) (da i γ)
  }