
\begin{code}[hide]
{-# OPTIONS --prop #-}
open import Lib
\end{code}

\begin{code}
record Monoid {A : Set} : Set₁ where
  field
    C : Set
    _∙_ : C → C → C
    assoc : {x y z : C} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    e : C
    idl : {x : C} → e ∙ x ≡ x
    idr : {x : C} → x ∙ e ≡ x
    η : A → C
\end{code}

\begin{code}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

assoc : ∀{A}{x y z : List A} → (x ++ y) ++ z ≡ x ++ (y ++ z)
assoc {A} {[]} {y} {z} = refl
assoc {A} {x ∷ xs} {y} {z} = cong (x ∷_) (assoc {A} {xs})

idr : ∀{A}{x : List A} → x ++ [] ≡ x
idr {A} {[]} = refl
idr {A} {x ∷ xs} = cong (x ∷_) (idr {A} {xs})

I : {A : Set} → Monoid {A}
I {A} = record
    { C = List A
    ; _∙_ = _++_
    ; assoc = λ {x} {y} {z} → assoc {A} {x} {y} {z}
    ; e = []
    ; idl = refl
    ; idr = idr
    ; η = _∷ []
    }
\end{code}

