{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib

data funar : ℕ → Set where
  zero : funar 0
  suc  : funar 1
  +'   : funar 2

data relar : ℕ → Set where
  eq   : relar 2
  leq  : relar 2

open import model

module workInSyntax where
  import Syntax funar relar as S
  open Model S.I

  zero' : ∀{Γ} → Tm Γ
  zero' {Γ} = fun {Γ} zero _

  suc' : ∀{Γ} → Tm Γ → Tm Γ
  suc' {Γ} n = fun {Γ} suc (n , _)

  three : ∀{Γ} → Tm Γ
  three {Γ} = suc' {Γ} (suc' {Γ} (suc' {Γ} (zero' {Γ})))

  Eq : ∀{Γ} → Tm Γ → Tm Γ → For Γ
  Eq {Γ} u v = Rel {Γ} eq (u , (v , _))

  Γ = ◇ ▹ₜ ▹ₚ Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})
  p : Pf Γ (Forall {Γ} (_⊃_ {Γ ▹ₜ} (Eq {Γ ▹ₜ} (qₜ {Γ}) (three {Γ ▹ₜ})) (Eq {Γ ▹ₜ} (qₜ {Γ}) (qₜ {◇} [ pₚ {◇ ▹ₜ}{Eq {◇ ▹ₜ} (qₜ {◇}) (three {◇ ▹ₜ})} ]ᵗ [ pₜ {◇ ▹ₜ} ]ᵗ))))
  p = {!!}

module workInTarski where

  ℕfun : (n : ℕ) → funar n → ℕ ^ n → ℕ
  ℕfun _ zero _ = zero
  ℕfun _ suc (n , _) = suc n
  ℕfun _ +' (m , n , _) = m + n

  ℕRel : (n : ℕ) → relar n → ℕ ^ n → Prop
  ℕRel _ eq (m , n , _) = m ≡ n
  ℕRel _ leq = {!!}

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
  p = {!!}

module workInAnyModel {i}{j}{k}(M : Model funar relar {i}{j}{k}) where
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
  p = {!!}
