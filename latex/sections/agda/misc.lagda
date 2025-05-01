
\begin{code}[hide]
{-# OPTIONS --prop #-}
module misc where
\end{code}

\newcommand{\miscUniversalQuantifier}{
\begin{code}
∀'_ : {A : Set} → (A → Prop) → Prop
∀' P = ∀ x → P x
\end{code}}

\newcommand{\miscExistentialQuantifier}{
\begin{code}
data ∃ (A : Set) (B : A → Prop) : Prop where
  _,_ : (a : A) → B a → ∃ A B
\end{code}}

\newcommand{\miscConjunction}{
\begin{code}
record _Σ_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B
\end{code}}

\newcommand{\miscDisjunction}{
\begin{code}
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
\end{code}}

\newcommand{\miscImplication}{
\begin{code}
_→'_ : Set → Set → Set
A →' B = A → B  -- Az Agda függvény típusa
\end{code}}

\begin{code}[hide]
postulate ⊥ : Set
\end{code}

\newcommand{\miscNegation}{
\begin{code}
¬_ : Set → Set
¬ A = A → ⊥
\end{code}}

\newcommand{\miscEquality}{
\begin{code}
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
\end{code}}

\newcommand{\miscExLemma}{
\begin{code}
lemma : {A : Set} {x : A} {P Q : A → Set} →
        (∀ x → P x → Q x) → (∀ x → P x) → ∀ x → Q x
lemma f g x = f x (g x)
\end{code}} 