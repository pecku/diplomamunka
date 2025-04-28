\begin{code}[hide]
{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib
open import model

module Tarski
\end{code}
\newcommand{\tmModuleParams}{
\begin{code}
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (D : Set)
  (fun : (n : ℕ) → funar n → D ^ n → D)
  (Rel : (n : ℕ) → relar n → D ^ n → Prop)
\end{code}
}

\begin{code}[hide]
  where

_$_ : {Γ : Set}{n : ℕ} → (Γ → D) ^ n → Γ → D ^ n
ds $ γ = map (λ d → d γ) ds
\end{code}

\newcommand{\tmTarski}{
\begin{AgdaAlign}
\vspace{1\baselineskip}
\AgdaNoSpaceAroundCode{}
\begin{code}
T : Model funar relar
T = record
     { Con = Set
     ; Sub = λ Δ Γ → Δ → Γ
\end{code}
\begin{code}[hide]
     ; _∘_ = λ γ δ θ → γ (δ θ)
     ; ass = refl
     ; id = λ γ → γ
     ; idl = refl
     ; idr = refl
     ; ◇ = 𝟙
     ; ε = _
     ; ◇η = refl
\end{code}
\begin{code}
     ; Tm = λ Γ → Γ → D
\end{code}
\begin{code}[hide]
     ; _[_]ᵗ = λ d γ δ → d (γ δ)
     ; [∘]ᵗ = refl
     ; [id]ᵗ = refl
     ; _▹ₜ = λ Γ → Γ × D
     ; _,ₜ_ = λ γ d δ → (γ δ , d δ)
     ; pₜ = fst
     ; qₜ = snd
     ; ▹ₜβ₁ = refl
     ; ▹ₜβ₂ = refl
     ; ▹ₜη = refl
\end{code}
\begin{code}
     ; For = λ Γ → Γ → Prop
\end{code}
\begin{code}[hide]
     ; _[_]ᶠ = λ A γ δ → A (γ δ)
     ; [∘]ᶠ = refl
     ; [id]ᶠ = refl
\end{code}
\begin{code}
     ; Pf = λ Γ A → (γ : Γ) → A γ
\end{code}
\begin{code}[hide]
     ; _[_]ᵖ = λ a γ δ → a (γ δ)
     ; _▹ₚ_ = λ Γ A → Σ Γ λ γ → Lift (A γ)
     ; _,ₚ_ = λ γ a δ → (γ δ , mk (a δ))
     ; pₚ = fst
     ; qₚ = λ γa → un (snd γa)
     ; ▹ₚβ₁ = refl
     ; ▹ₚη = refl
     ; Rel = λ ar ds γ → Rel _ ar (ds $ γ)
     ; Rel[] = funext λ δ → cong (Rel _ _) map∘
     ; fun = λ ar ds γ → fun _ ar (ds $ γ)
     ; fun[] = funext λ δ → cong (fun _ _) map∘
\end{code}
\begin{code}
     ; _⊃_ = λ A B γ → A γ → B γ
\end{code}
\begin{code}[hide]
     ; ⊃[] = refl
     ; ⊃in = λ b γ a → b (γ , mk a)
     ; ⊃out = λ f a γ → f γ (a γ)
\end{code}
\begin{code}
     ; _∧_ = λ A B γ → A γ ×p B γ
\end{code}
\begin{code}[hide]
     ; ∧[] = refl
     ; ∧in = λ a b γ → a γ ,p b γ
     ; ∧out₁ = λ ab γ → fst (ab γ)
     ; ∧out₂ = λ ab γ → snd (ab γ)
     ; ⊤ = λ _ → 𝟙p
     ; ⊤[] = refl
     ; ⊤in = λ _ → tt
\end{code}
\begin{code}
     ; _∨_ = λ A B γ → A γ ⊎p B γ
\end{code}
\begin{code}[hide]
     ; ∨[] = refl
     ; ∨in₁ = λ a γ → inl (a γ)
     ; ∨in₂ = λ b γ → inr (b γ)
     ; ∨out = λ ac bc ab γ → casep (λ a → ac (γ , mk a)) (λ b → bc (γ , mk b)) (ab γ)
     ; ⊥ = λ _ → 𝟘p
     ; ⊥[] = refl
     ; ⊥out = λ b γ → exfalsop (b γ)
\end{code}
\begin{code}
     ; Forall = λ A γ → (d : D) → A (γ , d)
\end{code}
\begin{code}[hide]
     ; Forall[] = refl
     ; ∀in = λ a γ d → a (γ , d)
     ; ∀out = λ a γd → a (fst γd) (snd γd)
\end{code}
\begin{code}
     ; ∃ = λ A γ → Σsp D λ d → A (γ , d)
\end{code}
\begin{code}[hide]
     ; ∃[] = refl
     ; ∃in = λ d a γ → d γ ,sp a γ
     ; ∃out = λ f da γ → casesp (λ d a → f ((γ , d) , mk a)) (da γ)
\end{code}
\hspace{6em} \vdots
\begin{code}
     }
\end{code}
\end{AgdaAlign}
\AgdaSpaceAroundCode{}
}