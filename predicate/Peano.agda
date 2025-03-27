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

  p : Pf (◇ ▹ₜ ▹ₚ Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})) (Forall (Eq qₜ three ⊃ Eq qₜ (qₜ [ pₚ ]ᵗ [ pₜ ]ᵗ)))
  p = ∀in (⊃in {!  !})

  A⊃A : {A : For ◇} → Pf (◇) (A ⊃ A)
  A⊃A = ⊃in qₚ
 
  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A {A}{B} = ⊃in (substP (λ x → Pf (◇ ▹ₚ A) (x)) (⊃[] ⁻¹) (⊃in {◇ ▹ₚ A}{B [ pₚ ]ᶠ}{A [ pₚ ]ᶠ} (qₚ [ pₚ ]ᵖ)))

  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (A ∧ B ⊃ B ∨ A)
  A∧B⊃B∨A {A}{B} = ⊃in (substP (λ x → Pf (◇ ▹ₚ A ∧ B) x) (∨[] ⁻¹) (∨in₁ (∧out₂ (substP (λ x → Pf (◇ ▹ₚ A ∧ B) x) ∧[] qₚ))))

  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
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
  
  -- (x,p:x=3) ⊢ ∀y.y=3⊃y=x
  p : Pf Γ (Forall {Γ} (_⊃_ {Γ ▹ₜ} (Eq {Γ ▹ₜ} (qₜ {Γ}) (three {Γ ▹ₜ})) (Eq {Γ ▹ₜ} (qₜ {Γ}) (qₜ {◇} [ pₚ {◇ ▹ₜ}{Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})} ]ᵗ [ pₜ {◇ ▹ₜ} ]ᵗ))))
  p = {!   !} --∀in (⊃in (∀out {! qₚ  !}))

  A⊃A : {A : For ◇} → Pf ◇ (_⊃_ {◇} A A)
  A⊃A = ⊃in qₚ

  A⊃B⊃A : {A B : For ◇} → Pf ◇ (_⊃_ {◇} A (_⊃_ {◇} B A)) --(A ⊃ B ⊃ A)
  A⊃B⊃A = ⊃in (⊃in (qₚ [ pₚ ]ᵖ))

  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (_⊃_ {◇} (_∧_ {◇} A B) (_∨_ {◇} A B) ) --(A ∧ B ⊃ B ∨ A)
  A∧B⊃B∨A = ⊃in (∨in₁ (∧out₁ qₚ))

  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) (_⊃_ {◇} (Forall {◇} (_∧_ {◇ ▹ₜ} P Q)) (_∧_ {◇} (Forall {◇} P) (Forall {◇} Q))) -- (Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q)
  ∀P∧Q⊃∀P∧∀Q = ⊃in (∧in (∀in (∧out₁ (∀out qₚ))) (∀in (∧out₂ (∀out qₚ))))

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

  A⊃B⊃A : {A B : For ◇} → Pf (◇) (A ⊃ B ⊃ A)
  A⊃B⊃A = ⊃in λ γ x → un (snd γ) 

  A∧B⊃B∨A : {A B : For ◇} → Pf (◇) (A ∧ B ⊃ B ∨ A)
  A∧B⊃B∨A = ⊃in λ γ → inl (snd (un (snd γ)))

  ∀P∧Q⊃∀P∧∀Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) ((Forall (P ∧ Q)) ⊃ (Forall P ∧ Forall Q))
  ∀P∧Q⊃∀P∧∀Q = λ γ x → (λ d → fst (x d)) ,p λ d → snd (x d)

  ∀P∧∀Q⊃∀P∧Q : {P Q : For (◇ ▹ₜ)} → Pf (◇) ((Forall P ∧ Forall Q) ⊃ (Forall (P ∧ Q)))
  ∀P∧∀Q⊃∀P∧Q = λ γ x d → fst x d ,p snd x d         


module workInBool where
  import BoolModel funar relar ℕ (λ n _ _ → n) (λ n _ _ → true) as B
  open Model B.B
  
  lem : ∀{Γ}{A : For Γ} → Pf Γ (A ∨ (A ⊃ ⊥))
  lem {Γ} {A} γ with A γ
  ... | false = refl
  ... | true = refl
  