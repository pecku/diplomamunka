\begin{code}[hide]
{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Lib

data funar : ℕ → Set where
  zero : funar 0
  suc  : funar 1
  +'   : funar 2

data relar : ℕ → Set where
  eq   : relar 2

open import model

module workInAnyModel {i}{j}{k}{l}(M : Model funar relar {i}{j}{k}{l}) where
  open Model M
  
  zero' : ∀{Γ} → Tm Γ
  zero' {Γ} = fun zero _

  suc' : ∀{Γ} → Tm Γ → Tm Γ
  suc' {Γ} n = fun {Γ} suc (n , _)

  three : ∀{Γ} → Tm Γ
  three {Γ} = suc' {Γ} (suc' {Γ} (suc' {Γ} (zero' {Γ})))

  Eq : ∀{Γ} → Tm Γ → Tm Γ → For Γ
  Eq {Γ} u v = Rel {Γ} eq (u , (v , _))

  A⊃A : {A : For ◇} → Pf (◇) (A ⊃ A)
  A⊃A = ⊃in qₚ
\end{code}
\newcommand{\pAnyE}{
\begin{code}
  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A {A}{B} =
    ⊃in (
        substP 
            (λ x → Pf (◇ ▹ₚ A) (x))
            (⊃[] ⁻¹)
            (⊃in {◇ ▹ₚ A}{B [ pₚ ]ᶠ}{A [ pₚ ]ᶠ} (qₚ [ pₚ ]ᵖ))
    )
\end{code}}
\begin{code}[hide]
  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (A ∧ B ⊃ B ∨ A)
  A∧B⊃B∨A {A}{B} = ⊃in (substP (λ x → Pf (◇ ▹ₚ A ∧ B) x) (∨[] ⁻¹) (∨in₁ (∧out₂ (substP (λ x → Pf (◇ ▹ₚ A ∧ B) x) ∧[] qₚ))))
\end{code}
\newcommand{\pAnyC}{
\begin{code}
  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} →
                Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
  ∀P∧Q⊃∀P∧∀Q {P}{Q} = 
    ⊃in
    (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) x) (∧[] ⁻¹)
      (∧in
        (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) x) (Forall[] ⁻¹)
          (∀in (∧out₁ (∀out
            (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) (Forall x)) ∧[]
              (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) x) Forall[] qₚ))))))
        (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) x) (Forall[] ⁻¹) 
          (∀in (∧out₂ (∀out
            (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) (Forall x)) ∧[]
              (substP (λ x → Pf (◇ ▹ₚ Forall (P ∧ Q)) x) Forall[] qₚ))))))))
\end{code}}

\begin{code}[hide]
module workInSyntax where
  import Syntax funar relar as S
  open Model S.I

  zero' : ∀{Γ} → Tm Γ
  zero' {Γ} = fun {Γ} zero _

  suc' : ∀{Γ} → Tm Γ → Tm Γ
  suc' {Γ} n = fun {Γ} suc ((n , _))

  three : ∀{Γ} → Tm Γ
  three {Γ} = suc' {Γ} (suc' {Γ} (suc' {Γ} (zero' {Γ})))

  Eq : ∀{Γ} → Tm Γ → Tm Γ → For Γ
  Eq {Γ} u v = Rel {Γ} eq (u , (v , _))

  Γ₀₁ = ◇ ▹ₚ (Forall {◇} (Forall {◇ ▹ₜ} (_⊃_ {◇ ▹ₜ ▹ₜ} (Eq {◇ ▹ₜ ▹ₜ} (qₜ {◇} [ pₜ {◇ ▹ₜ} ]ᵗ) (qₜ {◇ ▹ₜ}) ) (Eq {◇ ▹ₜ ▹ₜ} (qₜ {◇ ▹ₜ}) (qₜ {◇} [ pₜ {◇ ▹ₜ} ]ᵗ)))))
  
  Γ₀₂ = Γ₀₁ ▹ₚ (Forall {◇} (Forall {◇ ▹ₜ} (Forall {◇ ▹ₜ ▹ₜ} (_⊃_ {◇ ▹ₜ ▹ₜ ▹ₜ} (Eq {◇ ▹ₜ ▹ₜ ▹ₜ} (qₜ {◇} [ pₜ {◇ ▹ₜ} ]ᵗ [ pₜ {◇ ▹ₜ ▹ₜ} ]ᵗ) (qₜ {◇ ▹ₜ} [ pₜ {◇ ▹ₜ ▹ₜ} ]ᵗ)) (_⊃_ {◇ ▹ₜ ▹ₜ ▹ₜ} (Eq {◇ ▹ₜ ▹ₜ ▹ₜ} (qₜ {◇ ▹ₜ} [ pₜ {◇ ▹ₜ ▹ₜ} ]ᵗ) (qₜ {◇ ▹ₜ ▹ₜ})) (Eq {◇ ▹ₜ ▹ₜ ▹ₜ} (qₜ {◇} [ pₜ {◇ ▹ₜ} ]ᵗ [ pₜ {◇ ▹ₜ ▹ₜ} ]ᵗ) (qₜ {◇ ▹ₜ ▹ₜ})))))))
  
  Γ = Γ₀₂ ▹ₜ ▹ₚ Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})

  A⊃A : {A : For ◇} → Pf ◇ (_⊃_ {◇} A A)
  A⊃A = ⊃in qₚ
\end{code}
\newcommand{\pSynE}{
\begin{code}
  A⊃B⊃A : {A B : For ◇} → Pf ◇ (_⊃_ {◇} A (_⊃_ {◇} B A))
  A⊃B⊃A = ⊃in (⊃in (qₚ [ pₚ ]ᵖ))
\end{code}}
\begin{code}[hide]
  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (_⊃_ {◇} (_∧_ {◇} A B) (_∨_ {◇} A B) )
  A∧B⊃B∨A = ⊃in (∨in₁ (∧out₁ qₚ))
\end{code}
\newcommand{\pSynC}{
\begin{code}
  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) ( _⊃_ {◇}
        (Forall {◇} (_∧_ {◇ ▹ₜ} P Q))
        (_∧_ {◇} (Forall {◇} P) (Forall {◇} Q)))
  ∀P∧Q⊃∀P∧∀Q = ⊃in (∧in (∀in (∧out₁ (∀out qₚ))) (∀in (∧out₂ (∀out qₚ))))
\end{code}}

\begin{code}[hide]
module workInTarski where

  ℕfun : (n : ℕ) → funar n → ℕ ^ n → ℕ
  ℕfun _ zero _ = zero
  ℕfun _ suc (n , _) = suc n
  ℕfun _ +' (m , n , _) = m + n

  ℕRel : (n : ℕ) → relar n → ℕ ^ n → Prop
  ℕRel _ eq (m , n , _) = m ≡ n

  import Tarski funar relar ℕ ℕfun ℕRel as T
  open Model T.T
 
  zero' : ∀{Γ} → Tm Γ
  zero' {Γ} = fun zero _

  suc' : ∀{Γ} → Tm Γ → Tm Γ
  suc' {Γ} n = fun {Γ} suc (n , _)

  three : ∀{Γ} → Tm Γ
  three {Γ} = suc' {Γ} (suc' {Γ} (suc' {Γ} (zero' {Γ})))

  Eq : ∀{Γ} → Tm Γ → Tm Γ → For Γ
  Eq {Γ} u v = Rel {Γ} eq (u , (v , _))

  p : Pf (◇ ▹ₜ ▹ₚ Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})) (Forall (Eq qₜ three ⊃ Eq qₜ (qₜ [ pₚ ]ᵗ [ pₜ ]ᵗ)))
  p = λ γ d x → (un (snd γ) ◾ x ⁻¹) ⁻¹

  A⊃A : {A : For ◇} → Pf (◇) (A ⊃ A)
  A⊃A = ⊃in λ γ → un (snd γ) 
\end{code}
\newcommand{\pTarE}{
\begin{code}
  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A γ a b = a
\end{code}}
\begin{code}[hide]
  A⊃B⊃A' : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A' = ⊃in λ γ x → un (snd γ)
  
  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (A ∧ B ⊃ B ∨ A)
  A∧B⊃B∨A = ⊃in λ γ → inl (snd (un (snd γ)))
\end{code}
\newcommand{\pTarC}{
\begin{code}
  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} →
                Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
  ∀P∧Q⊃∀P∧∀Q γ x = (λ d → fst (x d)) ,p λ d → snd (x d)
\end{code}}
\begin{code}[hide]
  ∀P∧∀Q⊃∀P∧Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) ((Forall P ∧ Forall Q) ⊃ (Forall (P ∧ Q)))
  ∀P∧∀Q⊃∀P∧Q = λ γ x d → fst x d ,p snd x d         

module workInBool where
  import BoolModel funar relar ℕ (λ n _ _ → n) (λ n _ _ → true) as B
  open Model B.B
  
  lem : ∀{Γ}{A : For Γ} → Pf Γ (A ∨ (A ⊃ ⊥))
  lem {Γ} {A} γ with A γ
  ... | false = refl
  ... | true = refl
\end{code}
\newcommand{\pBooE}{
\begin{code}
  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A {A} {B} γ with A γ | B γ
  ... | false | false = refl
  ... | false | true = refl
  ... | true | false = refl
  ... | true | true = refl
\end{code}}
\begin{code}[hide]
  t&&t→t₁ : ∀{a b} → a && b ≡ true → a ≡ true
  t&&t→t₁ {true} {true} refl = refl
  t&&t→t₁ {false} {true} x = x
  t&&t→t₂ : ∀{a b} → a && b ≡ true → b ≡ true
  t&&t→t₂ {true} {true} refl = refl
  t&&t→t₂ {true} {false} x = x
\end{code}
\newcommand{\pBooC}{
\begin{code}
  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} →
                Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
  ∀P∧Q⊃∀P∧∀Q {P} {Q} γ =
    ind⊎p
      (λ x → case (λ _ → true) (λ _ → false)
        x => (Forall P ∧ Forall Q) γ ≡ true)
      (λ h₁ → ind⊎p
        (λ x → true => (case (λ _ → true) (λ _ → false)
            x && Forall Q γ)
          ≡ true)
        (λ h₂ → ind⊎p 
          (λ x → true => (true && case (λ _ → true) (λ _ → false) x)
            ≡ true)
          (λ h₃ → refl)
          (λ h₃ → exfalsop (h₃ λ d → t&&t→t₂ (h₁ d)))
          (B.lem ((d : ℕ) → Q (γ , d) ≡ true)))
        (λ h₂ → ind⊎p
          (λ x → true => (false && case (λ _ → true) (λ _ → false)
              x)
            ≡ true)
          (λ h₃ → exfalsop (h₂ λ d → t&&t→t₁ (h₁ d)))
          (λ h₃ → exfalsop (h₃ λ d → t&&t→t₂ (h₁ d)))
          (B.lem ((d : ℕ) → Q (γ , d) ≡ true)))
        (B.lem ((d : ℕ) → P (γ , d) ≡ true)))
      (λ h₁ → ind⊎p
        (λ x → false => (case (λ _ → true) (λ _ → false)
            x && Forall Q γ)
          ≡ true)
        (λ h₂ → ind⊎p
          (λ x → false => (true && case (λ _ → true) (λ _ → false)
            x) ≡ true)
          (λ h₃ → refl)
          (λ h₃ → refl)
          (B.lem ((d : ℕ) → Q (γ , d) ≡ true)))
        (λ h₂ → ind⊎p
          (λ x → false => (false && case (λ _ → true) (λ _ → false)
            x) ≡ true)
          (λ h₃ → refl)
          (λ h₃ → refl)
          (B.lem ((d : ℕ) → Q (γ , d) ≡ true)))
        (B.lem ((d : ℕ) → P (γ , d) ≡ true)))
      (B.lem ((d : ℕ) → (P (γ , d) && Q (γ , d)) ≡ true))
\end{code}}

\begin{code}[hide]
module workInFamily where
  ℕfun : (n : ℕ) → funar n → (i : ℕ) → ℕ ^ n → ℕ
  ℕfun _ zero _ _ = zero
  ℕfun _ suc _ (n , _) = suc n
  ℕfun _ +' _ (m , n , _) = m + n

  ℕRel : (n : ℕ) → relar n → (i : ℕ) → ℕ ^ n → Prop
  ℕRel _ eq _ (m , n , _) = m ≡ n

  import Family funar relar ℕ (λ I → ℕ) ℕfun ℕRel as F
  open Model F.F
\end{code}
\newcommand{\pFamE}{
\begin{code}
  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A i γ a b = a   
\end{code}}
\newcommand{\pFamC}{
\begin{code}
  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} →
                Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
  ∀P∧Q⊃∀P∧∀Q i γ x = (λ d → fst (x d)) ,p λ d → snd (x d)  
\end{code}}