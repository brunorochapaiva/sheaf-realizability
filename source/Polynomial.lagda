\begin{code}

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.Vector
open import UF.SubtypeClassifier

open import PAS

module Polynomial where

 -- Polynomials over a PAS
 data Poly {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) (n : ℕ) : 𝓤 ̇ where
  𝕧   : Fin n → Poly 𝒜 n
  𝕔   : ⟅ 𝒜 ⟆ → Poly 𝒜 n
  _·_ : Poly 𝒜 n → Poly 𝒜 n → Poly 𝒜 n

 infixl 20 _·_

 -- In this module we want to be explicit about the partial applicative
 -- structure
 module _ {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣
  open PASNotation 𝒜

  -- Evaluating a polynomial
  evaluate : Poly 𝒜 0 → 𝓛 ⟅ 𝒜 ⟆
  evaluate (𝕔 a)   = η a
  evaluate (t · r) = binary-Kleisli _⊕_ (evaluate t) (evaluate r)

  syntax evaluate 𝒜 t = ⟦ t ⟧[ 𝒜 ]

 -- Have to separate the following into a separate module so the syntax works
 -- correctly

 module _ {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣
  open PASNotation 𝒜

  -- Substitutions
  Sub : ℕ → ℕ → 𝓤 ̇
  Sub n m = Vector (Poly 𝒜 n) m

  -- Closed (total) substitutions
  CSub : ℕ → 𝓤 ̇
  CSub n = Vector ⟅ 𝒜 ⟆ n

  substitute : {n m : ℕ} → Sub m n → Poly 𝒜 n → Poly 𝒜 m
  substitute σ (𝕧 i)   = σ !! i
  substitute σ (𝕔 a)   = 𝕔 a
  substitute σ (t · r) = substitute σ t · substitute σ r

  to-sub : {n : ℕ} → CSub n → Sub 0 n
  to-sub = vmap 𝕔

  -- Apply multiple arguments in reverse order
  -- We expect `apply e [ a ; b ; c ]` to compute `((e ⊕ a) ⊕ b) ⊕ c`
  apply : {n : ℕ} → ⟅ 𝒜 ⟆ → CSub n → 𝓛 ⟅ 𝒜 ⟆
  apply a []      = η a
  apply a (x ∷ σ) = ((_⊕ x) ♯) (apply a σ)

  𝕔-is-defined : (a : ⟅ 𝒜 ⟆) → is-defined ⟦ 𝕔 a ⟧[ 𝒜 ]
  𝕔-is-defined a = ⋆

  ·-is-defined-left : (t r : Poly 𝒜 0)
                    → is-defined ⟦ t · r ⟧[ 𝒜 ]
                    → is-defined ⟦ t ⟧[ 𝒜 ]
  ·-is-defined-left t r =
   binary-Kleisli-is-defined-left (PAS-application 𝒜) ⟦ t ⟧[ 𝒜 ] ⟦ r ⟧[ 𝒜 ]

  ·-is-defined-right : (t r : Poly 𝒜 0)
                     → is-defined ⟦ t · r ⟧[ 𝒜 ]
                     → is-defined ⟦ r ⟧[ 𝒜 ]
  ·-is-defined-right t r =
   binary-Kleisli-is-defined-right (PAS-application 𝒜) ⟦ t ⟧[ 𝒜 ] ⟦ r ⟧[ 𝒜 ]

 module PolynomialNotation {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  open import Partiality 𝓣

  ⟦_⟧ : Poly 𝒜 0 → 𝓛 ⟅ 𝒜 ⟆
  ⟦_⟧ = evaluate 𝒜

\end{code}
