\begin{code}

open import MLTT.Spartan
open import UF.FunExt using (funext)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module Sheaf { 𝓤 : Universe} where

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

 module _ (topology : LT-topology) where

  open LTNotation topology

  is-sheaf : {𝓥 : Universe} (A : 𝓥 ̇) → 𝓤 ⁺ ⊔ 𝓥  ̇
  is-sheaf A =
   Σ glue ꞉ ((P : Ω 𝓤) → T P holds → (P holds → A) → A) ,
   ((P : Ω 𝓤) (p : T P holds) (x : A) → glue P p (λ _ → x) ＝ x)

  glue : {𝓥 : Universe} {A : 𝓥 ̇} → is-sheaf A → (P : Ω 𝓤) → T P holds → (P holds → A) → A
  glue = pr₁

  glue-unique : {𝓥 : Universe} {A : 𝓥 ̇} (h : is-sheaf A)
              → (P : Ω 𝓤) (p : T P holds) (x : A) → glue h P p (λ _ → x) ＝ x
  glue-unique = pr₂

  is-T-stable : Ω 𝓤 → 𝓤  ̇
  is-T-stable P = T P holds → P holds

  ΩT : 𝓤 ⁺ ̇
  ΩT = Σ P ꞉ Ω 𝓤 , is-T-stable P

  being-T-stable-is-prop : funext 𝓤 𝓤
                   → (P : Ω 𝓤) → is-prop (is-T-stable P)
  being-T-stable-is-prop fe P = Π-is-prop fe (λ _ → holds-is-prop P)

  to-Ω : ΩT → Ω 𝓤
  to-Ω = pr₁

  _holds' : ΩT → 𝓤  ̇
  _holds' = _holds ∘ to-Ω

  holds'-is-prop : (P : ΩT) → is-prop (P holds')
  holds'-is-prop = holds-is-prop ∘ to-Ω

  ΩT-elements-are-T-stable : (P : ΩT) → is-T-stable (to-Ω P)
  ΩT-elements-are-T-stable = pr₂

  to-ΩT-＝ : funext 𝓤 𝓤
          → {P Q : 𝓤 ̇ }
            {i : is-prop P} {j : is-prop Q}
            {h : is-T-stable (P , i)} {k : is-T-stable (Q , j)}
          → P ＝ Q
          → ((P , i) , h) ＝[ ΩT ] ((Q , j) , k)
  to-ΩT-＝ fe h = to-subtype-＝ (being-T-stable-is-prop fe) (to-Ω-＝ fe h)

  ΩT-extensionality : propext 𝓤
                    → funext 𝓤 𝓤
                    → {p q : ΩT}
                    → (p holds' → q holds')
                    → (q holds' → p holds')
                    → p ＝ q
  ΩT-extensionality pe fe {p} {q} f g =
   to-ΩT-＝ fe (pe (holds'-is-prop p) (holds'-is-prop q) f g)

  ΩT-is-sheaf : propext 𝓤 → funext 𝓤 𝓤 → is-sheaf ΩT
  ΩT-is-sheaf pe fe = ΩT-glue , ΩT-glue-unique
   where
    ΩT-glue : (P : Ω 𝓤) → T P holds → (P holds → ΩT) → ΩT
    ΩT-glue P p f = R , R-is-T-stable
     where
      Q : P holds → Ω 𝓤
      Q = pr₁ ∘ f

      Q-is-T-stable : (h : P holds) → is-T-stable (Q h)
      Q-is-T-stable = pr₂ ∘ f

      R : Ω 𝓤
      R = ((h : P holds) → (Q h) holds) ,
          Π-is-prop fe (λ h → holds-is-prop (Q h))

      R-is-T-stable : T R holds → R holds
      R-is-T-stable q h = Q-is-T-stable h (q ≫= λ r → η (r h))

    ΩT-glue-unique : (P : Ω 𝓤) (p : T P holds) (Q : ΩT)
                   → ΩT-glue P p (λ _ → Q) ＝ Q
    ΩT-glue-unique P p Q = ΩT-extensionality pe fe forward backward
     where
      forward : (P holds → Q holds') → Q holds'
      forward f = pr₂ Q (p ≫= (η ∘ f))

      backward : Q holds' → (P holds → Q holds')
      backward q _ = q

\end{code}
