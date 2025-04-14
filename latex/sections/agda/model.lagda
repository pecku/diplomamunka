
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

A termeket (\AgdaField{Tm}) egy funktorként adjuk meg. Úgy is mondhatjuk, hogy egy kontextustól függenek, mivel lehetnek benne termváltozók, amikbe be tudunk majd helyettesíteni, így értéket adva a szabad változóknak. Ehhez szükségünk lesz termekbe való behelyettesítésre, másnéven egy morfizmusok feletti akcióra. Egy funktornak teljesítenie kell két feltételt is: a kompozícióval való kompatibilitást és az identitással való kompatibilitást. Ezeket az \AgdaField{[∘]ᵗ} és \AgdaField{[id]ᵗ} egyenlőségek biztosítják.
\begin{code}
      Tm    : Con → Set k
      _[_]ᵗ : ∀{Γ Δ} → Tm Γ → Sub Δ Γ → Tm Δ
      [∘]ᵗ  : ∀{Γ Δ θ}{t : Tm Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ}
              → t [ γ ∘ δ ]ᵗ ≡ t [ γ ]ᵗ [ δ ]ᵗ
      [id]ᵗ : ∀{Γ}{t : Tm Γ} → t [ id ]ᵗ ≡ t
\end{code}
A környezetek termekkel és termváltozókkal való kiegészítését is megadjuk. A környezetbe betenni egy termváltozót (\AgdaField{\_▹ₜ}) hasonlítható egy olyan Descartes szorzathoz, amelynek az egyik oldalán az egyelemű halmaz található: \AgdaDatatype{\_×⊤}. A behelyettesítéseket is kiegészíthetjük termekkel (\AgdaField{\_,ₜ\_}), amelyeket ismételten a Descartes szorzattal lehetne azonosítani. A képzett pároknak tehát meg tudjuk adni az első (\AgdaField{pₜ}) és a második (\AgdaField{qₜ}) projekcióját.
\begin{code}
      _▹ₜ   : Con → Con
      _,ₜ_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▹ₜ)
      pₜ    : ∀{Γ} → Sub (Γ ▹ₜ) Γ
      qₜ    : ∀{Γ} → Tm (Γ ▹ₜ)
\end{code}

Fontos megadjuk a redukciós szabályokat is (β, η), hogy biztosítsuk az azonos kifejezések közötti egyenlőséget.

\texttt{
((p∘\_) , (q[\_])) : Sub Δ (Γ ▹ₜ) ≅ Sub Δ Γ × Tm Δ : \_,ₜ\_
}

\begin{itemize}
\item β: jobbról balra, majd jobbra = mintha nem történt volna semmi
\item η: balról jobbra, majd balra = mintha nem történt volna semmi
\end{itemize}
\begin{code}
      ▹ₜβ₁  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → pₜ ∘ (γ ,ₜ t) ≡ γ
      ▹ₜβ₂  : ∀{Γ Δ}{t : Tm Δ}{γ : Sub Δ Γ} → qₜ [ γ ,ₜ t ]ᵗ ≡ t
      ▹ₜη   : ∀{Γ Δ} → {γt : Sub Δ (Γ ▹ₜ)} → γt ≡ (pₜ ∘ γt ,ₜ qₜ [ γt ]ᵗ)
\end{code}

\subsection{De Bruijn-indexek}

A De Bruijn-indexek a változók lambda-kalkulus vagy logikai kifejezésekben való ábrázolásának egy módja. Fő előnye, hogy nem használ változóneveket. Ahelyett, hogy egy változóra névvel hivatkoznánk, minden változót egy számmal reprezentálunk, amely megadja, hogy hány kötőelemet (például kvantorokat) kell felfelé haladnunk a kifejezésfában, hogy megtaláljuk a változó értékét. A De Bruijn-indexek használata megkönnyíti a kifejezések manipulálását és egyszerűsíti a bizonyításokat, mivel nem fordul elő névütközés vagy változó-újradefiniálás.

Egy egyszerű példa:

A \texttt{λx. λy. x} kifejezés De Bruijn-indexekkel: \texttt{λ. λ. 1}.

Az 1 itt a két szinttel feljebb kötött változóra hivatkozik (0-tól indexelve), azaz az x-re.

Az indexelés a következőképp működik:

\begin{itemize}
\item A legbelső kötött változó a 0 indexet kapja.
\item Az azt követő az 1 indexet.
\item Aztán 2 és így tovább.
\end{itemize}

Tehát:

\begin{itemize}
\item A \texttt{λx. x} kifejezés \texttt{λ. 0} lesz.
\item A \texttt{λx. λy. x} kifejezés \texttt{λ. λ. 1} lesz.
\item A \texttt{λx. λy. y} kifejezés \texttt{λ. λ. 0} lesz.
\end{itemize}

\subsubsection{Miért "jobbak" a De Bruijn-indexek?}
Különösen az olyan formális rendszerekben, mint jelen esetben az elsőrendű logikai implementáció, a De Bruijn-indexek segítenek a következőkben:

\begin{itemize}
\item A változónevek ütközésének elkerülése

Egy helyettesítés végrehajtásakor az átnevezés (renaming, alfa konverzió) szükségtelenné válik. Nem kell többé aggódni a változók véletlen elfogása (variable capture) miatt.

\item Helyettesítések egyszerűbb végrehajtása

A helyettesítés következetessé válik. Nincs szükség a változók nevének nyomon követésére, csak az indexeket kell megfelelően eltolni a helyettesítés során.

\item Egyszerűbb egyenlőségellenőrzés

Két kifejezés az átnevezésig egyenlő, ha De Bruijn-ábrázolásaik megegyeznek. Mondhatni ingyen kapjuk az alfa-ekvivalenciát.

\item Jobban illik a mechanikus bizonyítási rendszerekhez
Az olyan rendszerek, mint az Agda, a Coq vagy a logikát belsőleg implementáló bizonyítási asszisztensek előnyben részesülnek a De Bruijn-indexek használatával kapcsolatban, mert:
\begin{itemize}
\item Függő típusos nyelvekben könnyebb őket megvalósítani
\item A mintaillesztés is kevésbé érzékeny a hibákra
\item Passzol a strukturális rekurziós elvekhez az olyan totális nyelvekben, mint az Agda.
\end{itemize}
\end{itemize}

Az univerzális kvantor szignatúrája tipikusan a következőképpen nézne ki:
\begin{lstlisting}
∀_ : Formula → Formula
\end{lstlisting}

De szemantikusan, a De Bruijn-indexelt környezetben, a ∀ köt egy változót a formulában, ami azt eredményezi, hogy egyel kevesebb szabad változó lesz benne, ami a szignatúrában is látszik:

\begin{lstlisting}
∀ : (A : For (Γ ▹ₜ)) → For Γ
\end{lstlisting}

Összességében esetünkben nagyban megkönnyíti a munkát a
\begin{itemize}
\item ∀ és ∃ implementálásánál és használatánál
\item behelyettesítésekkel kapcsolatos műveleteknél
\item formális bizonyításoknál
\end{itemize}

Jelen implementációban a De Bruijn-indexek megléte a következőképpen valósul meg:

\begin{itemize}
\item A \AgdaField{\_▹ₜ} művelet azáltal ad hozzá egy új változót a környezethez, hogy az indexeket eltolja egyel.
\item A \AgdaField{\_,ₜ\_} megfeltethető azzal, hogy az új változóhoz konstruálunk egy behelyettesítést.
\item A \AgdaField{pₜ} és \AgdaField{qₜ} pedig a projekciók, amelyek segítenek lebontani a behelyettesítést.
  \begin{itemize}
  \item \AgdaField{pₜ} eldobja a legújabb változót
  \item \AgdaField{qₜ} a változó a 0. indexen
  \end{itemize}
\end{itemize}

Ugyanez a megvalósítás látható a későbbiekben a bizonyítások esetében is.

\section{Formulák}

A formulákra is tekinthetünk funktorként, így hasonlóan a termekhez a következő módon adjuk meg:
\begin{code}
      For : Con → Set j
      _[_]ᶠ : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ
      [∘]ᶠ  : ∀{Γ Δ θ}{A : For Γ}{γ : Sub Δ Γ}{δ : Sub θ Δ}
              → A [ γ ∘ δ ]ᶠ ≡ A [ γ ]ᶠ [ δ ]ᶠ
      [id]ᶠ : ∀{Γ}{A : For Γ} → A [ id ]ᶠ ≡ A
\end{code}

\section{Bizonyítások}

A bizonyításokat már egy kicsivel bonyolultabban adjuk meg, ugyanis egy \AgdaField{For} feletti dependáns funktronak is nevezhetnénk. Ha vesszük például a Γ ⊢ A szokásos logikai (bizonyításelméleti) jelölést, akkor a \AgdaDatatype{p} : \AgdaField{Pf} Γ A azt jelenti, hogy \AgdaDatatype{p} bizonyítja az A állítást, ahol a szabad változók Γ-ban vannak.
\begin{code}
      Pf  : (Γ : Con) → For Γ → Prop l
      _[_]ᵖ : ∀{Γ Δ A} → Pf Γ A → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ)
\end{code}
A bizonyítás-változókat a termváltozók esetében is használt operációkhoz hasonlóan valósítjuk meg:
\begin{code}
      _▹ₚ_ : (Γ : Con) → For Γ → Con
      _,ₚ_  : ∀{Δ Γ A} → (γ : Sub Δ Γ) → Pf Δ (A [ γ ]ᶠ) → Sub Δ (Γ ▹ₚ A)
      pₚ    : ∀{Γ A} → Sub (Γ ▹ₚ A) Γ
      qₚ    : ∀{Γ A} → Pf (Γ ▹ₚ A) ((A [ pₚ ]ᶠ))
      ▹ₚβ₁ : ∀ {Γ Δ A}{γ : Sub Δ Γ}{a : Pf Δ (A [ γ ]ᶠ)} → pₚ ∘ (γ ,ₚ a) ≡ γ
      ▹ₚη  : ∀ {Γ Δ A}{γa : Sub Δ (Γ ▹ₚ A)}
             → γa ≡ (pₚ ∘ γa ,ₚ substP (Pf Δ) ([∘]ᶠ ⁻¹) (qₚ [ γa ]ᵖ))
\end{code}

\noindent
\raggedright
\texttt{
((p∘\_),(q[\_])) : Sub Δ (Γ▹ₚA) ≅ (γ: Sub Δ Γ) × Pf Δ (A[γ]ᶠ) : \_,ₚ\_
}

\section{Reláció- és függvényszimbólumok}

A modell a függvények és a relációk aritásával van felparaméterezve, ezt felhasználva határozzuk meg, hogy egy reláció vagy függvény hány termet vár majd paraméterként.
\begin{code}
      Rel   : ∀{Γ}{n : ℕ} → relar n → Tm Γ ^ n → For Γ
      Rel[] : ∀{Γ n}{ar : relar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ}
              → Rel ar ts [ γ ]ᶠ ≡ Rel ar (map _[ γ ]ᵗ ts)
      fun   : ∀{Γ}{n : ℕ} → funar n → Tm Γ ^ n → Tm Γ
      fun[] : ∀{Γ n}{ar : funar n}{ts : Tm Γ ^ n}{Δ}{γ : Sub Δ Γ}
              → fun ar ts [ γ ]ᵗ ≡ fun ar (map _[ γ ]ᵗ ts)
\end{code}

\section{Logikai összekötők}

\subsection{Implikáció (⊃)}

Az A ⊃ B jelentése: "ha A igaz, akkor B is igaz".
\begin{code}
      _⊃_   : ∀{Γ} → For Γ → For Γ → For Γ
\end{code}
\begin{code}
      ⊃[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ⊃ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ⊃ B [ γ ]ᶠ
\end{code}
\begin{itemize}
\item Az implikáció bevezető szabálya (\AgdaField{⊃in}): Ha tudjuk bizonyítani, hogy B igaz egy olyan kontextusban, ahol A feltételezett, akkor van egy bizonyításunk A ⊃ B-re is.
\begin{code}
      ⊃in   : ∀{Γ A B} → Pf (Γ ▹ₚ A) (B [ pₚ ]ᶠ) → Pf Γ ((A ⊃ B))
\end{code}
\item Az implikáció kivezető szabálya (\AgdaField{⊃out}): Ha van egy bizonyításunk A ⊃ B-re, valamint A-ra is, akkor van egy bizonyításunk B-re is.
\begin{code}
      ⊃out  : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B
\end{code}
\end{itemize}

\subsection{Konjunkció (∧)}
Az A ∧ B azt jelenti, hogy mind A, mind B igaz.
\begin{code}
      _∧_   : ∀{Γ} → For Γ → For Γ → For Γ
\end{code}
\begin{code}
      ∧[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ∧ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ∧ B [ γ ]ᶠ
\end{code}
\begin{itemize}
\item A konjunkció bevezető szabálya (\AgdaField{∧in}): Ha A és B külön-külön bizonyítható, akkor A ∧ B is igaz.
\begin{code}
      ∧in   : ∀{Γ A B} → Pf Γ A → Pf Γ B → Pf Γ (A ∧ B)
\end{code}
\item Az konjunkció kivezető szabálya (\AgdaField{∧out₁}): Az A ∧ B-ből következik A.
\item Az konjunkció kivezető szabálya (\AgdaField{∧out₂}): Az A ∧ B-ből következik B.
\begin{code}
      ∧out₁ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
      ∧out₂ : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
\end{code}
\end{itemize}

\subsection{Diszjunkció (∨)}
Az A ∨ B jelentése, hogy legalább az egyik (A vagy B) igaz.
\begin{code}
      _∨_   : ∀{Γ} → For Γ → For Γ → For Γ
\end{code}
\begin{code}
      ∨[]   : ∀{Γ A B Δ}{γ : Sub Δ Γ} → (A ∨ B) [ γ ]ᶠ ≡ A [ γ ]ᶠ ∨ B [ γ ]ᶠ
\end{code}
\begin{itemize}
\item A diszjunkció bevezető szabálya (\AgdaField{∨in₁}): Ha A igaz, akkor A ∨ B is igaz.
\item A diszjunkció bevezető szabálya (\AgdaField{∨in₂}): Ha B igaz, akkor A ∨ B is igaz.
\begin{code}
      ∨in₁  : ∀{Γ A B} → Pf Γ A → Pf Γ (A ∨ B)
      ∨in₂  : ∀{Γ A B} → Pf Γ B → Pf Γ (A ∨ B)
\end{code}
\item A diszjunkció kivezető szabálya (\AgdaField{∨out}): Ha tudjuk, hogy A ∨ B igaz, és abból is következik, ha A igaz, de abból is, ha B igaz, akkor C igaz.
\begin{code}
      ∨out  : ∀{Γ A B C} → Pf (Γ ▹ₚ A) (C [ pₚ ]ᶠ) → Pf (Γ ▹ₚ B) (C [ pₚ ]ᶠ)
              → Pf Γ (A ∨ B) → Pf Γ C
\end{code}
\end{itemize}

\subsection{Konstans igaz (⊤)}
A \AgdaField{⊤} egy mindig igaz állítást jelöl.
\begin{code}
      ⊤     : ∀{Γ} → For Γ
\end{code}
\begin{code}
      ⊤[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊤ [ γ ]ᶠ ≡ ⊤
\end{code}
\begin{itemize}
\item Az \textit{igaz} bevezető szabálya (\AgdaField{⊤in}): Minden kontextusban igaz.
\begin{code}
      ⊤in   : ∀{Γ} → Pf Γ ⊤
\end{code}
\end{itemize}

\subsection{Konstans hamis (⊥)}
Az \AgdaField{⊥} egy ellentmondást vagy hamis állítást jelöl.
\begin{code}
      ⊥     : ∀{Γ} → For Γ
\end{code}
\begin{code}
      ⊥[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊥ [ γ ]ᶠ ≡ ⊥
\end{code}
\begin{itemize}
\item A \textit{hamis} kivezető szabálya (\AgdaField{⊥out}): Ha egy bizonyítás során elérünk egy ellentmondást (\AgdaField{⊥}), akkor bármilyen tetszőleges állítást igaznak vehetünk (\textit{ex falso quodlibet}).
\begin{code}
      ⊥out  : ∀{Γ A} → Pf Γ ⊥ → Pf Γ A
\end{code}
\end{itemize}

\subsection{Kvantorok}

A kvantorok formális logikai eszközök, amelyek segítségével általános és létezési állításokat tehetünk. Bindernek (kötés) is nevezzük őket, utalva rá, hogy egy változót köt, azaz meghatározza, hogy egy változó miként értelmezhető egy adott hatókörben.

\subsubsection{Univerzális kvantor (∀)}

Az univerzális kvantor segítségével tudjuk kifejezni, hogy egy állítás minden lehetséges elemre igaz. Például a $∀x P(x)$ azt jelenti, hogy minden x-re igaz, hogy $P(x)$. A deklarációban látható is, hogy mivel egy kötésről beszélünk, egy formulában lévő szabad változót kötünk meg, így egy szűkebb kontextusban lévő formulát fogunk kapni.
\begin{code}
      Forall : ∀{Γ} → For (Γ ▹ₜ) → For Γ
\end{code}
\begin{code}
      Forall[] : ∀{Γ A Δ}{γ : Sub Δ Γ}
                 → Forall A [ γ ]ᶠ ≡ Forall (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
\end{code}
\begin{itemize}
\item Az univerzális kvantor bevezető szabálya (\AgdaField{∀in}):
\begin{code}
      ∀in : ∀{Γ A} → Pf (Γ ▹ₜ ) A → Pf Γ (Forall A)
\end{code}
\item Az univerzális kvantor kivezető szabálya (\AgdaField{∀out}):
\begin{code}
      ∀out : ∀{Γ A} → Pf Γ (Forall A) → Pf (Γ ▹ₜ ) A
\end{code}
\end{itemize}

\subsubsection{Egzisztenciális kvantor (∃)}

Az egzisztenciális kvantor azt fejezi ki, hogy létezik legalább egy olyan elem, amelyre igaz egy állítás. Például a $∃x P(x)$ azt jelenti, hogy létezik legalább egy x, amelyre igaz, hogy $P(x)$.
\begin{code}
      ∃ : ∀{Γ} → For (Γ ▹ₜ ) → For Γ
\end{code}
\begin{code}
      ∃[] : ∀{Γ A Δ}{γ : Sub Δ Γ} → ∃ A [ γ ]ᶠ ≡ ∃ (A [ γ ∘ pₜ ,ₜ qₜ ]ᶠ)
\end{code}
\begin{itemize}
\item Az egzisztenciális kvantor bevezető szabálya (\AgdaField{∃in}):
\begin{code}
      ∃in : ∀{Γ A} → (t : Tm Γ) → Pf Γ (A [ id ,ₜ t ]ᶠ) → Pf Γ (∃ A)
\end{code}
\item Az egzisztenciális kvantor kivezető szabálya (\AgdaField{∃out}):
\begin{code}
      ∃out : ∀{Γ A C} → Pf (Γ ▹ₜ ▹ₚ A) (C [ pₜ ∘ pₚ ]ᶠ) → Pf Γ (∃ A) → Pf Γ C
\end{code}
\end{itemize}

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