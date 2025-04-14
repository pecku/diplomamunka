
\begin{code}[hide]
open import Agda.Builtin.Equality
\end{code}

\begin{code}
record UP {A : Set} : Set₁ where
  field
    C : Set
    _,_ : A → A → C
    eq : {x y : A} → x , y ≡ y , x
\end{code}