
\begin{code}[hide]
{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib

module model
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

record Model {i}{j}{k}{l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
   field
\end{code}

\section{Kategória}

A modell fogalom első elemeként megadunk egy kontextusok és behelyettesítések által alkotott kategóriát. A kategória objektumait a kontextusok reprezentálják és a \AgdaField{Con} szort határozza meg. A morfizmusai pedig a behelyettesítések lesznek, amelyeket a \AgdaField{Sub} szort ad meg.
\begin{code}
      Con : Set i
      Sub : Con → Con → Set (k ⊔ l)
\end{code}
A kategóriákban a morfizmusoknak kell rendelkezniük egy kompozíciós művelettel (\AgdaField{\_∘\_}) is, amely két morfizmus összekapcsolását végzi el, ezzel létrehozva egy új morfizmust. 
\begin{code}
      _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      ass : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ}
            → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
\end{code}
Tehát, ha van egy morfizmus a Δ és Γ kontextusok között, valamint egy másik morfizmus a Θ és Δ között, akkor a kompozíciójuk egy új morfizmust ad a Θ és Γ kontextusok között. A kompozíciónak továbbá asszociatívnak kell lennie, amit az \AgdaField{ass} fejez ki.

A kategóriában minden objektumhoz léteznie kell egy olyan morfizmusnak, amely az objektumot önmagába képezi, ez lesz az identitás. Az identitás morfizmusnak a kompozícióval való alkalmazása nem változtathatja meg a kompozícióban szereplő másik morfizmust. Ezt az \AgdaField{idl} és \AgdaField{idr} egyenlőség biztosítja.
\begin{code}
      id  : ∀{Γ} → Sub Γ Γ
      idl : ∀{Γ Δ}{γ : Sub Δ Γ} → id ∘ γ ≡ γ
      idr : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ∘ id ≡ γ
\end{code}
A terminális objektum egy olyan objektum, amelyhez minden más objektumból létezik pontosan egy morfizmus. A mi esetünkben ez a terminális objektum a \AgdaField{◇}, a hozzá tartozó morfizmus pedig az \AgdaField{ε}. A morfizmus egyedülállóságát a \AgdaField{◇η} fogalmazza meg.
\begin{code}
      ◇   : Con
      ε   : ∀{Γ} → Sub Γ ◇
      ◇η  : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε
\end{code}

\section{Termek}





A termekbe való behelyettesítésre vonatkoznak.

A termek manipulálására vonatkozó szabályokat, valamint a kapcsolódó β és η szabályokat adjuk meg.



Megadjuk a termek kontextustól függő halmazát és a termek helyettesítését, amivel a szabad változóknak tudunk értéket adni. Megadjuk a helyettesítés funktort és az identitás behelyettesítésének lemmáját:
\begin{code}
      Tm    : Con → Set k
      _[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ
      [∘]ᵗ  : ∀{Γ Δ θ}{t : Tm Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ}
              → t [ γ ∘ δ ]ᵗ ≡ t [ γ ]ᵗ [ δ ]ᵗ
      [id]ᵗ : ∀{Γ}{t : Tm Γ} → t [ id ]ᵗ ≡ t
\end{code}
A környezetek termekkel és termváltozókkal való kiegészítését is megadjuk.
% környezetbe be tudunk tenni egy termváltozót (ez olyasmi, mint a Descartes szorzat _×⊤)
% _,_ = párképzés, mint a Descartes-szorzatnál
% p: első projekció (fst)
% q: második projekció (snd)

Két bétaszabály és egy étaszabály is tartozik ide:

((p∘\_) , (q[\_])) : Sub Δ (Γ ▹ₜ) ≅ Sub Δ Γ × Tm Δ : \_,ₜ\_

β: jobbrol balra, majd jobbra = mintha nem csinaltam volna semmit

η: balrol jobbra, majd balra = mintha nem csinaltam volna semmit
\begin{code}
      _▹ₜ   : Con → Con
      _,ₜ_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      pₜ    : ∀{Γ} → Sub (Γ ▹ₜ) Γ
      qₜ    : ∀{Γ} → Tm (Γ ▹ₜ)
      ▹ₜβ₁  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → pₜ ∘ (γ ,ₜ t) ≡ γ
      ▹ₜβ₂  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → qₜ [ γ ,ₜ t ]ᵗ ≡ t
      ▹ₜη   : ∀{Γ Δ} → {γt : Sub Δ (Γ ▹ₜ)} → γt ≡ (pₜ ∘ γt ,ₜ qₜ [ γt ]ᵗ)
\end{code}
Formulák:
\begin{code}
      For : Con → Set j
      _[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
      [∘]ᶠ  : ∀{Γ Δ θ}{A : For Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ}
              → A [ γ ∘ δ ]ᶠ ≡ A [ γ ]ᶠ [ δ ]ᶠ
      [id]ᶠ : ∀{Γ}{A : For Γ} → A [ id ]ᶠ ≡ A
\end{code}
Bizonyítások: ezekben vannak valtozok (Con-nal indexelve), es valamilyen formulat bizonyitanak (For-al indexelve)
      % Γ ⊢ A  <- szokasos logikai (bizonyitaslmeleti jeloles) p : Pf Γ A azt jelenti, hogy p bizonyitja az A allitast, ahol
      % szabad valtozok Γ-ban vannak
      % pl. Peano aritmetika (ahogy fent van megadva)
      %   relar 2 = 𝟚, false az egyenloseg, Rel {Γ}{2} false : Tm Γ × Tm Γ × ⊤ → For Γ
      %   zero := fun {Γ}{0} tt tt : Tm Γ
      %   suc (n : Tm Γ) := fun {Γ}{1} tt (n, tt) : Tm Γ
      %   Eq (u v : Tm Γ) := Rel {n = 2} false (u , v , tt)
      % (x,p:x=3) ⊢ ∀y.y=3 ⊃ y=x
      % ? : Pf (◇ ▹ₜ ▹ₚ Eq qₜ (suc (suc (suc zero)))) (Forall (Eq qₜ (suc (suc (suc zero))) ⊃ Eq qₜ (qₜ[pₜ][pₚ])))
\begin{code}
      Pf  : (Γ : Con) → For Γ → Prop l
      _[_]ᵖ : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)
\end{code}
Bizonyítás-változók:
      % ((p∘_) , (q[_])) : Sub Δ (Γ ▹ₚ A) ≅ (γ : Sub Δ Γ) × Pf Δ (A [ γ ]ᶠ) : _,ₚ_
\begin{code}
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      _,ₚ_  : ∀{Δ Γ A} → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ) → Sub Δ (Γ ▹ₚ A)
      pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
      qₚ    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))
      ▹ₚβ₁ : ∀ {Γ Δ A}{γ : Sub Δ Γ}{a : Pf Δ (A [ γ ]ᶠ)} → pₚ ∘ (γ ,ₚ a) ≡ γ
      ▹ₚη  : ∀ {Γ Δ A}{γa : Sub Δ (Γ ▹ₚ A)}
             → γa ≡ (pₚ ∘ γa ,ₚ substP (Pf Δ) ([∘]ᶠ ⁻¹) (qₚ [ γa ]ᵖ))
\end{code}
Reláció és függvényszimbólumok (a modell a függvények és a relációk aritásával van felparaméterezve):
\begin{code}
      Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ
      Rel[] : ∀{Γ n}{ar : relar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ}
              → Rel ar ts [ γ ]ᶠ ≡ Rel ar (map _[ γ ]ᵗ ts)
      fun   : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ
      fun[] : ∀{Γ n}{ar : funar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ}
              → fun ar ts [ γ ]ᵗ ≡ fun ar (map _[ γ ]ᵗ ts)
\end{code}
Logikai összekötők
\begin{code}
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
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ)
              → Pf Γ (A ∨ B) → Pf Γ C

      ⊥     : ∀{Γ} → For Γ
      ⊥[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊥ [ γ ]ᶠ ≡ ⊥
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A

      Forall : ∀{Γ} → For (Γ ▹ₜ) → For Γ
      Forall[] : ∀{Γ A Δ}{γ : Sub Δ Γ}
                 → Forall A [ γ ]ᶠ ≡ Forall (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
      ∀in : ∀{Γ A} → Pf (Γ ▹ₜ ) A → Pf Γ (Forall A)
      ∀out : ∀{Γ A} → Pf Γ (Forall A) → Pf (Γ ▹ₜ ) A

      ∃ : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
      ∃[] : ∀{Γ A Δ}{γ : Sub Δ Γ} → ∃ A [ γ ]ᶠ ≡ ∃ (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
      ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
      ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) (C [ pₜ ∘ pₚ ]ᶠ) → Pf Γ (∃ A) → Pf Γ C
\end{code}
\begin{code}[hide]
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
\end{code}