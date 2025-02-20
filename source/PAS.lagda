\begin{code}

open import MLTT.Spartan
open import UF.Sets

open import Partiality

module PAS where

 PAS : (𝓣 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓣 ⁺ ̇
 PAS 𝓣 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A × (A → A → 𝓛 𝓣 A)

 ⟅_⟆ : {𝓣 𝓤 : Universe} → PAS 𝓣 𝓤 → 𝓤 ̇
 ⟅_⟆ = pr₁

 PAS-is-set : {𝓣 𝓤 : Universe} → (𝒜 : PAS 𝓣 𝓤) → is-set ⟅ 𝒜 ⟆
 PAS-is-set 𝒜 = pr₁ (pr₂ 𝒜)

 PAS-application : {𝓣 𝓤 : Universe} → (𝒜 : PAS 𝓣 𝓤) → ⟅ 𝒜 ⟆ → ⟅ 𝒜 ⟆ → 𝓛 𝓣 ⟅ 𝒜 ⟆
 PAS-application 𝒜 = pr₂ (pr₂ 𝒜)

 syntax PAS-application 𝒜 a b = a ⊕[ 𝒜 ] b

 module PASNotation {𝓣 𝓤 : Universe} (𝒜 : PAS 𝓣 𝓤) where

  A : 𝓤 ̇
  A = ⟅ 𝒜 ⟆

  A-is-set : is-set A
  A-is-set = PAS-is-set 𝒜

  _⊕_ : A → A → 𝓛 𝓣 A
  a ⊕ b = a ⊕[ 𝒜 ] b

\end{code}
