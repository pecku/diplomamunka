{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib

module model
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

-- funar 0 = konstansszimbólumok halmaza
-- funar 1 = 1-paraméteres függvényszimbólumok halmaza
-- funar 2 = 2-paraméteres függvényszimbólumok halmaza
-- ...
-- relar 0 = alapállítások halmaza
-- relar 1 = predikátumszimbólumok halmaza
-- relar 2 = bináris relációszimbólumok halmaza
-- ...

-- pl. Peano aritmetika:
-- funar 0 = 1    zero : Nat
-- funar 1 = 1    suc  : Nat → Nat
-- funar 2 = 3    _+_, _*_, _^_ : Nat → Nat → Nat
-- funar _ = 0
-- relar 0 = 0
-- relar 1 = 0
-- relar 2 = 2    _<_, _=_ : Nat → Nat → Prop

record Model {i}{j}{k}{l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
   field
      -- kategoria:
      Con : Set i
      Sub : Con → Con → Set (k ⊔ l)
      _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      ass : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
      id  : ∀{Γ} → Sub Γ Γ
      idl : ∀{Γ Δ}{γ : Sub Δ Γ} → id ∘ γ ≡ γ
      idr : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ∘ id ≡ γ
      
      -- terminalis objektum van a kategoriaban:
      ◇   : Con
      ε   : ∀{Γ} → Sub Γ ◇
      ◇η  : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε

      -- termek
      Tm    : Con → Set k -- kornyezettol fuggo termek halmaza
      _[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ -- termek helyettesitese (szabad valtozoknak tudunk vele erteket adni)
      [∘]ᵗ  : ∀{Γ Δ θ}{t : Tm Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ} → t [ γ ∘ δ ]ᵗ ≡ t [ γ ]ᵗ [ δ ]ᵗ  -- a helyettesites funktor
      [id]ᵗ : ∀{Γ}{t : Tm Γ} → t [ id ]ᵗ ≡ t
      -- termvaltozok:
      _▹ₜ   : Con → Con -- kornyezetbe be tudunk tenni egy termvaltozot (ez olyasmi, mint a Descartes szorzat _×⊤)
      -- ((p∘_) , (q[_])) : Sub Δ (Γ ▹ₜ) ≅ Sub Δ Γ × Tm Δ : _,ₜ_
      -- β: jobbrol balra, majd jobbra = mintha nem csinaltam volna semmit
      -- η: balrol jobbra, majd balra = mintha nem csinaltam volna semmit
      -- p: elso projekcio (fst)
      -- q: elso projekcio (snd)
      -- _,_ = parkepzes, mint a Descartes-szorzatnal
      _,ₜ_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      pₜ    : ∀{Γ} → Sub (Γ ▹ₜ) Γ
      qₜ    : ∀{Γ} → Tm (Γ ▹ₜ)
      ▹ₜβ₁  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → pₜ ∘ (γ ,ₜ t) ≡ γ
      ▹ₜβ₂  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → qₜ [ γ ,ₜ t ]ᵗ ≡ t
      ▹ₜη   : ∀{Γ Δ} → {γt : Sub Δ (Γ ▹ₜ)} → γt ≡ (pₜ ∘ γt ,ₜ qₜ [ γt ]ᵗ)

      -- formulak:
      For : Con → Set j
      _[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
      [∘]ᶠ  : ∀{Γ Δ θ}{A : For Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ} → A [ γ ∘ δ ]ᶠ ≡ A [ γ ]ᶠ [ δ ]ᶠ
      [id]ᶠ : ∀{Γ}{A : For Γ} → A [ id ]ᶠ ≡ A

      -- bizonyitasok: ezekben vannak valtozok (Con-nal indexelve), es valamilyen formulat bizonyitanak (For-al indexelve)
      -- Γ ⊢ A  <- szokasos logikai (bizonyitaslmeleti jeloles) p : Pf Γ A azt jelenti, hogy p bizonyitja az A allitast, ahol
      -- szabad valtozok Γ-ban vannak
      -- pl. Peano aritmetika (ahogy fent van megadva)
      --   relar 2 = 𝟚, false az egyenloseg, Rel {Γ}{2} false : Tm Γ × Tm Γ × ⊤ → For Γ
      --   zero := fun {Γ}{0} tt tt : Tm Γ
      --   suc (n : Tm Γ) := fun {Γ}{1} tt (n, tt) : Tm Γ
      --   Eq (u v : Tm Γ) := Rel {n = 2} false (u , v , tt)
      -- (x,p:x=3) ⊢ ∀y.y=3 ⊃ y=x
      -- ? : Pf (◇ ▹ₜ ▹ₚ Eq qₜ (suc (suc (suc zero)))) (Forall (Eq qₜ (suc (suc (suc zero))) ⊃ Eq qₜ (qₜ[pₜ][pₚ])))
      Pf  : (Γ : Con) → For Γ → Prop l
      _[_]ᵖ : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)
      -- bizonyitas-valtozok:
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      -- ((p∘_) , (q[_])) : Sub Δ (Γ ▹ₚ A) ≅ (γ : Sub Δ Γ) × Pf Δ (A [ γ ]ᶠ) : _,ₚ_
      _,ₚ_  : ∀{Δ Γ A} → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ) → Sub Δ (Γ ▹ₚ A)
      pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
      qₚ    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))
      ▹ₚβ₁ : ∀ {Γ Δ A}{γ : Sub Δ Γ}{a : Pf Δ (A [ γ ]ᶠ)} → pₚ ∘ (γ ,ₚ a) ≡ γ
      ▹ₚη  : ∀ {Γ Δ A}{γa : Sub Δ (Γ ▹ₚ A)} → γa ≡ (pₚ ∘ γa ,ₚ substP (Pf Δ) ([∘]ᶠ ⁻¹) (qₚ [ γa ]ᵖ))

      -- relacio es fgv.szimbolumok
      Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ
      Rel[] : ∀{Γ n}{ar : relar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ} → Rel ar ts [ γ ]ᶠ ≡ Rel ar (map _[ γ ]ᵗ ts)
      fun   : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ
      fun[] : ∀{Γ n}{ar : funar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ} → fun ar ts [ γ ]ᵗ ≡ fun ar (map _[ γ ]ᵗ ts)

      -- logikai osszekotok
   
      _⊃_   : ∀{Γ} → For Γ → For Γ → For Γ
      ⊃[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ⊃ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ⊃ B [ γ ]ᶠ
      ⊃in   : ∀{Γ A B} → Pf (Γ ▹ₚ A) (B [ pₚ ]ᶠ) → Pf Γ ((A ⊃ B))
      ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B

      _∧_   : ∀{Γ} → For Γ → For Γ → For Γ
      ∧[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ∧ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ∧ B [ γ ]ᶠ
      ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
      ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
      ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B

      ⊤     : ∀{Γ} → For Γ
      ⊤[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊤ [ γ ]ᶠ ≡ ⊤
      ⊤in   : ∀{Γ} → Pf Γ ⊤

      _∨_   : ∀{Γ} → For Γ → For Γ → For Γ
      ∨[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ∨ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ∨ B [ γ ]ᶠ
      ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
      ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ) → Pf Γ (A ∨ B) → Pf Γ C

      ⊥     : ∀{Γ} → For Γ
      ⊥[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊥ [ γ ]ᶠ ≡ ⊥
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A

      Forall : ∀{Γ} → For (Γ ▹ₜ) → For Γ
      Forall[] : ∀{Γ A Δ}{γ : Sub Δ Γ} → Forall A [ γ ]ᶠ ≡ Forall (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
      ∀in : ∀{Γ A} → Pf (Γ ▹ₜ ) A → Pf Γ (Forall A)
      ∀out : ∀{Γ A} → Pf Γ (Forall A) → Pf (Γ ▹ₜ ) A

      ∃ : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
      ∃[] : ∀{Γ A Δ}{γ : Sub Δ Γ} → ∃ A [ γ ]ᶠ ≡ ∃ (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
      ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
      ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) (C [ pₜ ∘ pₚ ]ᶠ) → Pf Γ (∃ A) → Pf Γ C
      
{-
      Rel : {n : ℕ} → relar n → Tm Γ → Tm Γ → ... → Tm Γ → For Γ
                                \______________________/
                                          n db

      Rel : {n : ℕ} → relar n → For (◇ ▹ₜ ▹ₜ ... ▹ₜ)

      Tms : Con → ℕ → Set

      Rel : {n : ℕ} → relar n → Tms Γ n → For Γ

      Tms Γ 0 ≅ ⊤
      Tms Γ (1+n) ≅ Tms Γ n × Tm Γ
-}

   infixl 5 _▹ₚ_
   infixl 5 _,ₚ_
   infixl 5 _▹ₜ
   infixl 5 _,ₜ_
   infixr 6 _∘_
   infixr 6 _⊃_
   infixr 7 _∨_
   infixr 8 _∧_
   infixl 9 _[_]ᶠ
   infixl 9 _[_]ᵖ
   infixl 9 _[_]ᵗ
