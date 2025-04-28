\begin{code}[hide]
{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Lib
open import model

module BoolModel
\end{code}
\newcommand{\bmModuleParams}{
\begin{code}
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (D : Set)
  (fun : (n : ℕ) → funar n → D ^ n → D)
  (Rel : (n : ℕ) → relar n → D ^ n → Bool)
\end{code}
}

\begin{code}[hide]
  where

_$_ : {Γ : Set}{n : ℕ} → (Γ → D) ^ n → Γ → D ^ n
ds $ γ = map (λ d → d γ) ds

⊃in : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Σ Γ (λ γ₁ → Lift (A γ₁ ≡ true))) → B (fst γ) ≡ true) → (γ : Γ) → (A γ => B γ) ≡ true
⊃in {Γ} {A} {B} b γ with A γ in eq1
... | false with B γ
... | false = refl
... | true = refl
⊃in {Γ} {A} {B} b γ | true with B γ in eq2 | b (γ , mk eq1)
... | false | ()
... | true | refl = refl

⊃out : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Γ) → (A γ => B γ) ≡ true) → ((γ : Γ) → A γ ≡ true) → (γ : Γ) → B γ ≡ true
⊃out {Γ} {A} {B} ab a γ with A γ | B γ | ab γ | a γ
... | false | false | refl | ()
... | false | true | refl | ()
... | true | false | () | w
... | true | true | refl | refl = refl

∧in : {Γ : Set}{A : Γ → Bool}{B : Γ → Bool} → ((γ : Γ) → A γ ≡ true) → ((γ : Γ) → B γ ≡ true) → (γ : Γ) → (A γ && B γ) ≡ true
∧in {Γ} {A} {B} a b γ with A γ | B γ | a γ | b γ
... | false | false | () | w
... | false | true | () | w
... | true | false | refl | ()
... | true | true | refl | refl = refl

∧out₁ : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Γ) → (A γ && B γ) ≡ true) → (γ : Γ) → A γ ≡ true
∧out₁ {Γ} {A} {B} ab γ with A γ | B γ | ab γ
... | false | false | ()
... | false | true | ()
... | true | false | ()
... | true | true | refl = refl

∧out₂ : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Γ) → (A γ && B γ) ≡ true) → (γ : Γ) → B γ ≡ true
∧out₂ {Γ} {A} {B} ab γ with A γ | B γ | ab γ
... | false | false | ()
... | false | true | ()
... | true | false | ()
... | true | true | refl = refl

∨in₁ : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Γ) → A γ ≡ true) → (γ : Γ) → (A γ || B γ) ≡ true
∨in₁ {Γ} {A} {B} a γ with A γ | B γ | a γ
... | false | false | ()
... | false | true | ()
... | true | false | refl = refl
... | true | true | refl = refl

∨in₂ : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} → ((γ : Γ) → B γ ≡ true) → (γ : Γ) → (A γ || B γ) ≡ true
∨in₂ {Γ} {A} {B} b γ with A γ | B γ | b γ
... | false | false | ()
... | false | true | refl = refl
... | true | false | ()
... | true | true | refl = refl

∨out : {Γ : Set} {A : Γ → Bool} {B : Γ → Bool} {C : Γ → Bool} →
      ((γ : Σ Γ (λ γ₁ → Lift (A γ₁ ≡ true))) → C (fst γ) ≡ true) →
      ((γ : Σ Γ (λ γ₁ → Lift (B γ₁ ≡ true))) → C (fst γ) ≡ true) →
      ((γ : Γ) → (A γ || B γ) ≡ true) → (γ : Γ) → C γ ≡ true
∨out {Γ} {A} {B} {C} ac bc ab γ with A γ in eq1 | B γ in eq2
... | false | true = bc (γ , mk eq2)
... | true | false = ac (γ , mk eq1)
... | true | true = ac (γ , mk eq1)
... | false | false with C γ in eq3
... | true = refl
... | false with ab γ
... | x = cong₂ (_||_) eq1 eq2 ⁻¹ ◾ x

⊥out : {Γ : Set} {A : Γ → Bool} → ((γ : Γ) → false ≡ true) → (γ : Γ) → A γ ≡ true
⊥out {Γ} {A} b γ with A γ | b γ
... | false | ()
... | true | ()
\end{code}

\newcommand{\bmLem}{
\begin{code}
postulate
  lem : (A : Prop) → A ⊎ (A → 𝟘p)
\end{code}}

\newcommand{\bmForall}{
\begin{code}
Forall : {Γ : Set} → (Γ × D → Bool) → Γ → Bool
Forall F γ with lem ((d : D) → F(γ , d) ≡ true)
... | inl x = true
... | inr x = false
\end{code}}

\begin{code}[hide]
Forall[]' : {Γ : Set} {A : Γ × D → Bool} {Δ : Set} {γ : Δ → Γ} → (δ : Δ) → Forall A (γ δ) ≡ Forall (λ δ₁ → A (γ (fst δ₁) , snd δ₁)) δ
Forall[]' {Γ} {A} {Δ} {γ} δ with lem ((d : D) → A(γ δ , d) ≡ true)
... | inl x = refl
... | inr x = refl

Forall[] : {Γ : Set} {A : Γ × D → Bool} {Δ : Set} {γ : Δ → Γ} → (λ δ → Forall A (γ δ)) ≡ Forall (λ δ → A (γ (fst δ) , snd δ))
Forall[] = funext Forall[]'

∀in : {Γ : Set} {A : Γ × D → Bool} → ((γ : Γ × D) → A γ ≡ true) → (γ : Γ) → Forall A γ ≡ true
∀in {A = A} a γ with lem ((d : D) → A (γ , d) ≡ true)
... | inl x = refl
... | inr x = exfalsop (x λ d → a (γ , d))

∀out : {Γ : Set} {A : Γ × D → Bool} → ((γ : Γ) → Forall A γ ≡ true) → (γd : Γ × D) → A γd ≡ true
∀out {Γ} {A} a γd with A γd in eq1 | lem ((d : D) → A (fst γd , d) ≡ true) | a (fst γd)
... | false | inl x | _ = eq1 ⁻¹ ◾ x (snd γd)
... | false | inr x | ()
... | true | inl x | _ = refl
... | true | inr x | _ = refl
\end{code}

\newcommand{\bmExists}{
\begin{code}
∃ : {Γ : Set} → (Γ × D → Bool) → Γ → Bool
∃ A γ with lem ((Σsp D λ d → A (γ , d) ≡ true))
... | inl x = true
... | inr x = false
\end{code}}

\begin{code}[hide]
∃[]' : {Γ : Set} {A : Γ × D → Bool} {Δ : Set} {γ : Δ → Γ} → (δ : Δ) → ∃ A (γ δ) ≡ ∃ (λ δ₁ → A (γ (fst δ₁) , snd δ₁)) δ
∃[]' {Γ} {A} {Δ} {γ} δ with lem ((Σsp D λ d → A (γ δ , d) ≡ true))
... | inl x = refl
... | inr x = refl

∃[] : {Γ : Set} {A : Γ × D → Bool} {Δ : Set} {γ : Δ → Γ} → (λ δ → ∃ A (γ δ)) ≡ ∃ (λ δ → A (γ (fst δ) , snd δ))
∃[] = funext ∃[]'

∃in : {Γ : Set} {A : Γ × D → Bool} (t : Γ → D) → ((γ : Γ) → A (γ , t γ) ≡ true) → (γ : Γ) → ∃ A γ ≡ true
∃in {Γ} {A} t a γ with lem ((Σsp D λ d → A (γ , d) ≡ true))
... | inl x = refl
... | inr x = exfalsop (x (t γ ,sp a γ))

∃out : {Γ : Set} {A : Γ × D → Bool} {C : Γ → Bool} →
      ((γ : Σ (Γ × D) (λ γ₁ → Lift (A γ₁ ≡ true))) →
       C (fst (fst γ)) ≡ true) →
      ((γ : Γ) → ∃ A γ ≡ true) → (γ : Γ) → C γ ≡ true
∃out {Γ} {A} {C} c a γ with C γ in eq1 | lem ((Σsp D λ d → A (γ , d) ≡ true)) | a γ
... | false | inl (d ,sp x) | _ = eq1 ⁻¹ ◾ c ((γ , d) , mk x)
... | false | inr x | ()
... | true | inl x | _ = refl
... | true | inr x | _ = refl
\end{code}

\newcommand{\bmBoolModel}{
\begin{AgdaAlign}
\vspace{1\baselineskip}
\AgdaNoSpaceAroundCode{}
\begin{code}
B : Model funar relar
B = record
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
     ; For = λ Γ → Γ → Bool
\end{code}
\begin{code}[hide]
     ; _[_]ᶠ = λ A γ δ → A (γ δ)
     ; [∘]ᶠ = refl
     ; [id]ᶠ = refl
\end{code}
\begin{code}
     ; Pf = λ Γ A → (γ : Γ) → A γ ≡ true
\end{code}
\begin{code}[hide]
     ; _[_]ᵖ = λ a γ δ → a (γ δ)
     ; _▹ₚ_ = λ Γ A → Σ Γ λ γ → Lift (A γ ≡ true)
     ; _,ₚ_ = λ γ a δ → γ δ , mk (a δ)
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
     ; _⊃_ = λ A B γ → A γ => B γ
\end{code}
\begin{code}[hide]
     ; ⊃[] = refl
     ; ⊃in = ⊃in
     ; ⊃out = ⊃out
\end{code}
\begin{code}
     ; _∧_ = λ A B γ → A γ && B γ
\end{code}
\begin{code}[hide]
     ; ∧[] = refl
     ; ∧in = ∧in
     ; ∧out₁ = ∧out₁
     ; ∧out₂ = ∧out₂
     ; ⊤ = λ _ → true
     ; ⊤[] = refl
     ; ⊤in = λ _ → refl
\end{code}
\begin{code}
     ; _∨_ = λ A B γ → A γ || B γ
\end{code}
\begin{code}[hide]
     ; ∨[] = refl
     ; ∨in₁ = ∨in₁
     ; ∨in₂ = ∨in₂
     ; ∨out = ∨out
     ; ⊥ = λ _ → false
     ; ⊥[] = refl
     ; ⊥out = ⊥out
\end{code}
\begin{code}
     ; Forall = Forall
\end{code}
\begin{code}[hide]
     ; Forall[] = Forall[]
     ; ∀in = ∀in
     ; ∀out = ∀out
\end{code}
\begin{code}
     ; ∃ = ∃
\end{code}
\begin{code}[hide]
     ; ∃[] = ∃[]     
     ; ∃in = ∃in
     ; ∃out = ∃out
\end{code}
\hspace{6em} \vdots
\begin{code}
     }
\end{code}
\end{AgdaAlign}
\AgdaSpaceAroundCode{}
}