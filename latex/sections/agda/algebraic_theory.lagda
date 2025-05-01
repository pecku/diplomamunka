\begin{code}[hide]
open import Agda.Builtin.Equality
module algebraic_theory where
\end{code}

Egy algebrai elméletet szortok, operátorok és egyenletek határoznak meg. Egy elmélet modelljeit vagy algebráit algebrai struktúrának is szokás nevezni, ez minden szorthoz egy halmazt, az operátorokhoz függvényeket, az egyenletekhez pedig egyenlőségeket rendel.

Például a félcsoport egy olyan algebrai struktúra, amely egy halmazból és a rajta értelmezett asszociatív bináris műveletből áll. Ebben az esetben az asszociativitás lesz az az egyenlőség, amelyet a félcsoportnak teljesítenie kell.

\begin{code}
record Semigroup : Set₁ where
  field
    C : Set
    _∙_ : C → C → C
    associativity : (x y z : C) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
\end{code}

Ezek alapján a ℕ és a + (összeadás), vagy a 𝔹 (Bool) és az ∧ (és) félcsoportot alkotnak. Ez nem mondható el viszont a ℕ és a - (kivonás) párosításról, ugyanis az utóbbi műveletre nem igaz, hogy asszociatív.

Az előbb említett félcsoportokat egy-egy modellként is reprezentálhatjuk a következő módon:

\begin{code}[hide]
open import Agda.Builtin.Nat public renaming (Nat to ℕ) public

cong : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

+-assoc : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)
\end{code}
\begin{code}
ℕ+ : Semigroup
ℕ+ = record
  { C = ℕ
  ; _∙_ = _+_
  ; associativity = +-assoc
  }
\end{code}

A szintaxis egy olyan modell, amelyből minden más modellbe megy egy függvény megőrizve az operátorokat. A félcsoport szintaxisát a 0 elemű halmazzal tudjuk megadni. A 0 elemű halmazon meg tudunk adni mintaillesztéssel tetszőleges más halmazba függvényt, amely triviálisan megőrzi az összes operátort. 
\begin{code}
data C : Set where

I : Semigroup
I = record
  { C = C
  ; _∙_ = λ x y → x
  ; associativity = λ x y z → refl
  }  
\end{code}