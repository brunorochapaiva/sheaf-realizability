\begin{code}

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.Vector
open import UF.Sets
open import UF.SubtypeClassifier

module PCA (𝓤 𝓣 : Universe) where

open import Lifting.Construction 𝓣
open import Lifting.Monad 𝓣
open import Partiality 𝓣

PAS : 𝓤 ⁺ ⊔ 𝓣 ⁺ ̇
PAS = Σ A ꞉ 𝓤 ̇ , is-set A × (A → A → 𝓛 A)

module PASNotation (𝔸 : PAS) where
 A : 𝓤 ̇
 A = pr₁ 𝔸

 A-is-set : is-set A
 A-is-set = pr₁ (pr₂ 𝔸)

 _⊕_ : A → A → 𝓛 A
 _⊕_ = pr₂ (pr₂ 𝔸)

module Polynomial (𝔸 : PAS) where
 open PASNotation 𝔸

 -- Polynomials over a PAS
 data Poly (n : ℕ) : 𝓤 ̇ where
  𝕧   : Fin n → Poly n
  𝕔   : A → Poly n
  _·_ : Poly n → Poly n → Poly n

 infixl 20 _·_

 -- Substitutions
 Sub : ℕ → ℕ → 𝓤 ̇
 Sub n m = Vector (Poly n) m

 substitute : {n m : ℕ}
            → Sub m n
            → Poly n
            → Poly m
 substitute σ (𝕧 i)   = σ !! i
 substitute σ (𝕔 a)   = 𝕔 a
 substitute σ (t · r) = substitute σ t · substitute σ r

 -- Apply multiple arguments in reverse order
 -- We expect `apply e [ a ; b ; c ]` to compute `((e ⊕ a) ⊕ b) ⊕ c`
 apply : {n : ℕ} → A → Vector A n → 𝓛 A
 apply a []      = η a
 apply a (x ∷ σ) = ((_⊕ x) ♯) (apply a σ)

 to-sub : {n : ℕ} → Vector A n → Sub 0 n
 to-sub = vmap 𝕔

 -- Evaluating a polynomial
 ⟦_⟧ : Poly 0 → 𝓛 A
 ⟦ 𝕔 a ⟧   = η a
 ⟦ t · r ⟧ = binary-Kleisli _⊕_ ⟦ t ⟧ ⟦ r ⟧

 𝕔-is-defined : (a : A) → is-defined ⟦ 𝕔 a ⟧
 𝕔-is-defined a = ⋆

 ·-is-defined-left : (t r : Poly 0)
                   → is-defined ⟦ t · r ⟧
                   → is-defined ⟦ t ⟧
 ·-is-defined-left t r = binary-Kleisli-is-defined-left _⊕_ ⟦ t ⟧ ⟦ r ⟧

 ·-is-defined-right : (t r : Poly 0)
                   → is-defined ⟦ t · r ⟧
                   → is-defined ⟦ r ⟧
 ·-is-defined-right t r = binary-Kleisli-is-defined-right _⊕_ ⟦ t ⟧ ⟦ r ⟧

module FunctionalCompleteness (𝔸 : PAS) where

 open PASNotation 𝔸
 open Polynomial 𝔸
 open Relations A-is-set

 functionally-complete-structure : (𝓤 ⊔ 𝓣) ̇
 functionally-complete-structure = {n : ℕ} →
  Π t ꞉ Poly (succ n) , Σ e ꞉ A , Π xs ꞉ Vector A (succ n) ,
   is-defined (apply e (tail xs)) × ⟦ substitute (to-sub xs) t ⟧ ≼ apply e xs

module PCA where

 PCA-structure : (𝔸 : PAS) → 𝓤 ⊔ 𝓣  ̇
 PCA-structure 𝔸 = Σ 𝕜 ꞉ A , Σ 𝕤 ꞉ A ,
    ((a b : A) → ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 b ⟧ ≡ η a)
  × ((a b : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b ⟧)
  × ((a b c : A) → ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b · 𝕔 c  ⟧ ≼ ⟦ 𝕔 𝕤 · 𝕔 c · (𝕔 b · 𝕔 c) ⟧)
  where
   open PASNotation 𝔸
   open Polynomial 𝔸
   open Relations A-is-set

 PCA : 𝓤 ⁺ ⊔ 𝓣 ⁺  ̇
 PCA = Σ PCA-structure

 module PCANotation (𝔸 : PCA) where

  open PASNotation (pr₁ 𝔸)
  open Polynomial (pr₁ 𝔸)
  open Relations A-is-set

  𝕜 : A
  𝕜 = pr₁ (pr₂ 𝔸)

  𝕤 : A
  𝕤 = pr₁ (pr₂ (pr₂ 𝔸))

  k-law₁ : (a b : A) → ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 b ⟧ ≡ η a
  k-law₁ = pr₁ (pr₂ (pr₂ (pr₂ 𝔸)))

  k-law₀ : (a : A) → is-defined (⟦ 𝕔 𝕜 · 𝕔 a ⟧)
  k-law₀ a = ·-is-defined-left (𝕔 𝕜 · 𝕔 a) (𝕔 𝕜)
   (≡-is-defined-left ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 𝕜  ⟧ (η a) (k-law₁ a 𝕜))

  s-law₁ : (a b : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b ⟧
  s-law₁ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))

  s-law₀ : (a : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a  ⟧
  s-law₀ a = ·-is-defined-left (𝕔 𝕤 · 𝕔 a) (𝕔 𝕜) (s-law₁ a 𝕜)

  s-law₂ : (a b c : A) → ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b · 𝕔 c  ⟧ ≼ ⟦ 𝕔 𝕤 · 𝕔 c · (𝕔 b · 𝕔 c) ⟧
  s-law₂ = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))


\end{code}
