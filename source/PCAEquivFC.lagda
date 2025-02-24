\begin{code}

open import MLTT.Spartan
open import MLTT.Vector
open import MLTT.Fin

open import PAS
open import Polynomial
open import PCA
open import FC

module PCAEquivFC {𝓣 𝓤 : Universe} {𝒜 : PAS 𝓣 𝓤} where

 open import Partiality 𝓣
 open PASNotation 𝒜
 open PolynomialNotation 𝒜

 module _ (fc : FC-structure 𝒜) where

  private
   k-poly : Poly 𝒜 2
   k-poly = 𝕧 Fin.𝟎

   k : A
   k = reify fc k-poly

   k-spec : (a b : A) → ⟦ 𝕔 k · 𝕔 a · 𝕔 b ⟧ ≡ η a
   k-spec a b = ≡-symm (η a) ⟦ 𝕔 k · 𝕔 a · 𝕔 b ⟧
     (is-defined-≼-implies-≡ (η a) ⟦ 𝕔 k · 𝕔 a · 𝕔 b ⟧
      ⋆ (reify-spec fc k-poly (a ∷ (b ∷ []))))

   s-poly : Poly 𝒜 3
   s-poly = 𝕧 Fin.𝟎 · 𝕧 (Fin.suc (Fin.suc Fin.𝟎))
             · (𝕧 (Fin.suc Fin.𝟎) · 𝕧 (Fin.suc (Fin.suc Fin.𝟎)))

   s : A
   s = reify fc s-poly

   s-spec₁ : (a b : A) → is-defined ⟦ 𝕔 s · 𝕔 a · 𝕔 b ⟧
   s-spec₁ a b = reify-is-defined fc s-poly (a ∷ (b ∷ []))

   s-spec₂ : (a b c : A)
           →  ⟦ 𝕔 a · 𝕔 c · (𝕔 b · 𝕔 c) ⟧ ≼ ⟦ 𝕔 s · 𝕔 a · 𝕔 b · 𝕔 c ⟧
   s-spec₂ a b c = reify-spec fc s-poly (a ∷ (b ∷ (c ∷ [])))


  FC-to-PCA : PCA-structure 𝒜
  FC-to-PCA = k , s , k-spec , s-spec₁ , s-spec₂

 module _ (pca : PCA-structure 𝒜) where

  open PCAStructureNotation {𝒜 = 𝒜} pca

  private

   𝕜⊕ : A → A
   𝕜⊕ a = value (𝕜 ⊕ a) III
    where
     I : binary-Kleisli _⊕_ (η 𝕜) (η a) ≼ 𝕜 ⊕ a
     I = pr₁ (binary-Kleisli-η-both _⊕_ 𝕜 a)

     II : is-defined ⟦ 𝕔 𝕜 · 𝕔 a ⟧
     II = k-law₀ {𝒜 = 𝒜} pca a

     III : is-defined (𝕜 ⊕ a)
     III = ≼-preserves-defined ⟦ 𝕔 𝕜 · 𝕔 a ⟧ (𝕜 ⊕ a) I II

   abs-single : {n : ℕ} → Poly 𝒜 (succ n) → Poly 𝒜 n
   abs-single (𝕧 𝟎)       = 𝕔 𝕤 · 𝕔 𝕜 · 𝕔 𝕜
   abs-single (𝕧 (suc n)) = 𝕔 𝕜 · 𝕧 n
   abs-single (𝕔 a)       = 𝕔 𝕜 · 𝕔 a
   abs-single (t · r)     = 𝕔 𝕤 · abs-single t · abs-single r

   abs-single-spec : {n : ℕ} (t : Poly 𝒜 (succ n)) (x : A) (xs : CSub 𝒜 n)
                   → ⟦ substitute 𝒜 (to-sub 𝒜 (x ∷ xs)) t ⟧
                     ≼ ⟦ substitute 𝒜 (to-sub 𝒜 xs) (abs-single t) · 𝕔 x ⟧
   abs-single-spec (𝕧 𝟎) x xs = {!!}
    where
     goal : η x ≼ ⟦ 𝕔 𝕤 · 𝕔 𝕜 · (𝕔 𝕜 · 𝕔 x) ⟧
     goal = {!!}

     I : ⟦ 𝕔 x ⟧ ≼ ⟦ 𝕔 𝕜 · 𝕔 x · 𝕔 (𝕜⊕ x) ⟧
     I = ≡-implies-≼ ⟦ 𝕔 x ⟧ ⟦ 𝕔 𝕜 · 𝕔 x · 𝕔 (𝕜⊕ x) ⟧
          (≡-symm ⟦ 𝕔 𝕜 · 𝕔 x · 𝕔 (𝕜⊕ x) ⟧ ⟦ 𝕔 x ⟧
           (k-law₁ {𝒜 = 𝒜} pca x (𝕜⊕ x)))

     II : ⟦ 𝕔 𝕜 · 𝕔 x · 𝕔 (𝕜⊕ x) ⟧ ≼ ⟦ 𝕔 𝕜 · 𝕔 x · (𝕔 𝕜 · 𝕔 x) ⟧
     II = {!!}

     III : ⟦ 𝕔 𝕜 · 𝕔 x · (𝕔 𝕜 · 𝕔 x) ⟧ ≼ ⟦ 𝕔 𝕤 · 𝕔 𝕜 · 𝕔 𝕜 · 𝕔 x ⟧
     III = s-law₂ {𝒜 = 𝒜} pca 𝕜 𝕜 x
   abs-single-spec (𝕧 (suc n)) x xs = {!!}
   abs-single-spec (𝕔 a) x xs = {!!}
   abs-single-spec (t · r) x xs = {!!}

   abs : {n : ℕ} → Poly 𝒜 (succ n) → A
   abs t = {!!}

   abs-is-defined : {n : ℕ} (t : Poly 𝒜 (succ n)) (xs : CSub 𝒜 n)
                  → is-defined (apply 𝒜 (abs t) xs)
   abs-is-defined = {!!}

   abs-spec : {n : ℕ} (t : Poly 𝒜 (succ n)) (xs : CSub 𝒜 (succ n))
            → ⟦ substitute 𝒜 (to-sub 𝒜 xs) t ⟧ ≼ apply 𝒜 (abs t) xs
   abs-spec = {!!}

  PCA-to-FC : FC-structure 𝒜
  PCA-to-FC t =  abs t , abs-is-defined t , abs-spec t
\end{code}
