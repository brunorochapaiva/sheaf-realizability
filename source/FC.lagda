\begin{code}

open import MLTT.Spartan
open import MLTT.Vector

module FC {𝓣 𝓤 : Universe} where

 open import PAS
 open import Polynomial

 -- Functionally complete structure
 FC-structure : (𝒜 : PAS 𝓣 𝓤) → 𝓤 ⊔ 𝓣 ̇
 FC-structure 𝒜 = {n : ℕ} →
  Π t ꞉ Poly 𝒜 (succ n) , Σ e ꞉ A ,
     (Π xs ꞉ CSub 𝒜 n , is-defined (apply 𝒜 e xs))
   × (Π xs ꞉ CSub 𝒜 (succ n) , ⟦ substitute 𝒜 (to-sub 𝒜 xs) t ⟧ ≼ apply 𝒜 e xs)
  where
   open import Partiality 𝓣
   open PASNotation 𝒜
   open PolynomialNotation 𝒜


 module _ {𝒜 : PAS 𝓣 𝓤} (fc : FC-structure 𝒜) where

  open import Partiality 𝓣
  open PASNotation 𝒜
  open PolynomialNotation 𝒜

  reify : {n : ℕ} → Poly 𝒜 (succ n) → A
  reify t = pr₁ (fc t)

  reify-is-defined : {n : ℕ} (t : Poly 𝒜 (succ n)) (xs : CSub 𝒜 n)
                   → is-defined (apply 𝒜 (reify t) xs)
  reify-is-defined t xs = pr₁ (pr₂ (fc t)) xs

  reify-spec : {n : ℕ} (t : Poly 𝒜 (succ n)) (xs : CSub 𝒜 (succ n))
             → ⟦ substitute 𝒜 (to-sub 𝒜 xs) t ⟧ ≼ apply 𝒜 (reify t) xs
  reify-spec t xs = pr₂ (pr₂ (fc t)) xs

\end{code}
