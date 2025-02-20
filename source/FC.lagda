\begin{code}

open import MLTT.Spartan
open import MLTT.Vector

module FC where

 open import PAS
 open import Polynomial

 module _ {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣
  open PASNotation 𝒜
  open PolynomialNotation 𝒜

  -- Functionally complete structure
  FC-structure : 𝓤 ⊔ 𝓣 ̇
  FC-structure = {n : ℕ} →
   Π t ꞉ Poly 𝒜 (succ n) , Σ e ꞉ A , Π xs ꞉ CSub 𝒜 (succ n) ,
      is-defined (apply 𝒜 e (tail xs))
    × ⟦ substitute 𝒜 (to-sub 𝒜 xs) t ⟧ ≼ apply 𝒜 e xs

\end{code}
