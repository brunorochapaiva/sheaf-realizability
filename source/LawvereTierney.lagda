\begin{code}

open import MLTT.Spartan
open import UF.SubtypeClassifier
open import UF.Logic

open Conjunction

module LawvereTierney {𝓤 : Universe} where

 -- Lawvere-Tierney topology
 LT-topology : 𝓤 ⁺ ̇
 LT-topology =
  Σ T ꞉ (Ω 𝓤 → Ω 𝓤) ,
   ((P : Ω 𝓤) → P holds → T P holds) ×
   ((P Q : Ω 𝓤) → T P holds → (P holds → T Q holds) → T Q holds)

 T[_] : LT-topology → (Ω 𝓤 → Ω 𝓤)
 T[_] = pr₁

 ret : (topology : LT-topology)
      → (P : Ω 𝓤) → P holds → T[ topology ] P holds
 ret topology = pr₁ (pr₂ topology)

 bind : (topology : LT-topology)
       → (P Q : Ω 𝓤) → T[ topology ] P holds → (P holds → T[ topology ] Q holds) → T[ topology ] Q holds
 bind topology = pr₂ (pr₂ topology)

 module LTNotation (topology : LT-topology) where

  T : Ω 𝓤 → Ω 𝓤
  T = T[ topology ]

  η : {P : Ω 𝓤} → P holds → T P holds
  η = ret topology _

  _≫=_ : {P Q : Ω 𝓤} → T P holds → (P holds → T Q holds) → T Q holds
  _≫=_ = bind topology _ _

  T-action : {P Q : Ω 𝓤} → (P holds → Q holds) → T P holds → T Q holds
  T-action f = _≫= (η ∘ f)

  T-pair : {P Q : Ω 𝓤} → T P holds → T Q holds → T (P ∧ Q) holds
  T-pair r s = r ≫= (λ p → T-action (p ,_) s)

\end{code}
