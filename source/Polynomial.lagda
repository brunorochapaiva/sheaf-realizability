\begin{code}

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.Vector

open import PAS

module Polynomial where

 -- Polynomials over a PAS
 data Poly {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) (n : ℕ) : 𝓤 ̇ where
  𝕧   : Fin n → Poly 𝒜 n
  𝕔   : ⟅ 𝒜 ⟆ → Poly 𝒜 n
  _·_ : Poly 𝒜 n → Poly 𝒜 n → Poly 𝒜 n

 infixl 20 _·_

 module _ {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣
  open PASNotation 𝒜

  -- Evaluating a polynomial
  evaluate : Poly 𝒜 0 → 𝓛 ⟅ 𝒜 ⟆
  evaluate (𝕔 a)   = η a
  evaluate (t · r) = binary-Kleisli _⊕_ (evaluate t) (evaluate r)

  syntax evaluate 𝒜 t = ⟦ t ⟧[ 𝒜 ]

 module PolynomialNotation {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣

  ⟦_⟧ : Poly 𝒜 0 → 𝓛 ⟅ 𝒜 ⟆
  ⟦_⟧ = evaluate 𝒜


 module _ {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣
  open PASNotation 𝒜
  open PolynomialNotation 𝒜

  -- Substitutions
  Sub : ℕ → ℕ → 𝓤 ̇
  Sub n m = Vector (Poly 𝒜 n) m

  substitute : {n m : ℕ} → Sub m n → Poly 𝒜 n → Poly 𝒜 m
  substitute σ (𝕧 i)   = σ !! i
  substitute σ (𝕔 a)   = 𝕔 a
  substitute σ (t · r) = substitute σ t · substitute σ r

  -- Closed (total) substitutions
  CSub : ℕ → 𝓤 ̇
  CSub n = Vector A n

  to-sub : {n : ℕ} → CSub n → Sub 0 n
  to-sub = vmap 𝕔

  to-csub : {n : ℕ} (σ : Sub 0 n)
          → ((p : Fin n) → is-defined ⟦ σ !! p ⟧)
          → CSub n
  to-csub []      h = []
  to-csub (x ∷ σ) h = value ⟦ x ⟧ (h 𝟎) ∷ to-csub σ (h ∘ suc)

  -- Apply multiple arguments in order
  -- We expect `apply e [ a ; b ; c ]` to compute `((e ⊕ a) ⊕ b) ⊕ c`
  apply-poly : {n m : ℕ} → Poly 𝒜 m → Sub m n → Poly 𝒜 m
  apply-poly e []      = e
  apply-poly e (x ∷ σ) = apply-poly (e · x) σ

  apply : {n : ℕ} → A → CSub n → 𝓛 A
  apply e σ = ⟦ apply-poly (𝕔 e) (to-sub σ) ⟧

  𝕔-is-defined : (a : A) → is-defined ⟦ 𝕔 a ⟧
  𝕔-is-defined a = ⋆

  ·-is-defined-left : (t r : Poly 𝒜 0)
                    → is-defined ⟦ t · r ⟧
                    → is-defined ⟦ t ⟧
  ·-is-defined-left t r =
   binary-Kleisli-is-defined-left (PAS-application 𝒜) ⟦ t ⟧ ⟦ r ⟧

  ·-is-defined-right : (t r : Poly 𝒜 0)
                     → is-defined ⟦ t · r ⟧
                     → is-defined ⟦ r ⟧
  ·-is-defined-right t r =
   binary-Kleisli-is-defined-right (PAS-application 𝒜) ⟦ t ⟧ ⟦ r ⟧

  csubstitute-≼ : {n : ℕ} (t : Poly 𝒜 n) (σ : Sub 0 n)
               → (h : (p : Fin n) → is-defined ⟦ σ !! p ⟧)
               → ⟦ substitute (to-sub (to-csub σ h)) t ⟧
                  ≼ ⟦ substitute σ t ⟧
  csubstitute-≼ (𝕧 𝟎)       (x ∷ σ) h = (λ _ → h 𝟎) , λ _ → refl
  csubstitute-≼ (𝕧 (suc n)) (x ∷ σ) h = csubstitute-≼ (𝕧 n) σ (h ∘ suc)
  csubstitute-≼ (𝕔 a)   σ h = ≼-refl ⟦ 𝕔 a ⟧
  csubstitute-≼ (t · r) σ h = binary-Kleisli-≼
   ⟦ substitute (to-sub (to-csub σ h)) t ⟧
   ⟦ substitute σ t ⟧
   ⟦ substitute (to-sub (to-csub σ h)) r ⟧
   ⟦ substitute σ r ⟧
   _⊕_
   (csubstitute-≼ t σ h)
   (csubstitute-≼ r σ h)

  substitute-≼ : {n : ℕ} (t : Poly 𝒜 n) (σ : Sub 0 n)
               → (h : (p : Fin n) → is-defined ⟦ σ !! p ⟧)
               → ⟦ substitute σ t ⟧
                  ≼ ⟦ substitute (to-sub (to-csub σ h)) t ⟧
  substitute-≼ (𝕧 𝟎)       (x ∷ σ) h =
   (λ _ → ⋆) , (λ ϕ → ap (value ⟦ x ⟧) (being-defined-is-prop ⟦ x ⟧ ϕ (h 𝟎)))
  substitute-≼ (𝕧 (suc n)) (x ∷ σ) h = substitute-≼ (𝕧 n) σ (h ∘ suc)
  substitute-≼ (𝕔 a)   σ h = ≼-refl ⟦ 𝕔 a ⟧
  substitute-≼ (t · r) σ h = binary-Kleisli-≼
   ⟦ substitute σ t ⟧
   ⟦ substitute (to-sub (to-csub σ h)) t ⟧
   ⟦ substitute σ r ⟧
   ⟦ substitute (to-sub (to-csub σ h)) r ⟧
   _⊕_
   (substitute-≼ t σ h)
   (substitute-≼ r σ h)

\end{code}
