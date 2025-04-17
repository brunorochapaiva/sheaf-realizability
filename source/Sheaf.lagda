\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt using (funext)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open import LawvereTierney

module Sheaf {𝓤 : Universe} (topology : LT-topology) where
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


  record sheafification-exist : 𝓤ω where
   field
    𝓓 : {𝓥 : Universe} → 𝓥 ̇ → 𝓥 ̇

    -- Constructors (note that 𝐞 is a higher constructor)

    β : {𝓥 : Universe} {A : 𝓥 ̇}
      → A → 𝓓 A

    ǫ : {𝓥 : Universe} {A : 𝓥 ̇}
        (P : Ω 𝓤) → T P holds → (P holds → 𝓓 A) → 𝓓 A

    𝐞 : {𝓥 : Universe} {A : 𝓥 ̇}
        (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A) → ǫ P p (λ _ → d) ＝ d

    -- Dependent eliminator

    𝓓rec : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} (F : 𝓓 A → 𝓦 ̇)
           (hβ : (a : A) → F (β a))
           (hǫ : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
               → ((q : P holds) → F (ϕ q))
               → F (ǫ P p ϕ))
           (h𝐞 : (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A) (h : F d)
               → transport F (𝐞 P p d) (hǫ P p (λ _ → d) (λ _ → h)) ＝ h)
         → (d : 𝓓 A) → F d

    -- Computation rules for the eliminator

    𝓓rec-β : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} (F : 𝓓 A → 𝓦 ̇)
             (hβ : (a : A) → F (β a))
             (hǫ : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
                 → ((q : P holds) → F (ϕ q))
                 → F (ǫ P p ϕ))
             (h𝐞 : (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A) (h : F d)
                 → transport F (𝐞 P p d) (hǫ P p (λ _ → d) (λ _ → h)) ＝ h)
             (a : A)
           → 𝓓rec F hβ hǫ h𝐞 (β a) ＝ hβ a

    𝓓rec-ǫ : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} (F : 𝓓 A → 𝓦 ̇)
             (hβ : (a : A) → F (β a))
             (hǫ : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
                 → ((q : P holds) → F (ϕ q))
                 → F (ǫ P p ϕ))
             (h𝐞 : (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A) (h : F d)
                 → transport F (𝐞 P p d) (hǫ P p (λ _ → d) (λ _ → h)) ＝ h)
             (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
           → 𝓓rec F hβ hǫ h𝐞 (ǫ P p ϕ) ＝ hǫ P p ϕ (λ q → 𝓓rec F hβ hǫ h𝐞 (ϕ q))

    𝓓rec-𝐞 : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} (F : 𝓓 A → 𝓦 ̇)
             (hβ : (a : A) → F (β a))
             (hǫ : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
                 → ((q : P holds) → F (ϕ q))
                 → F (ǫ P p ϕ))
             (h𝐞 : (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A) (h : F d)
                 → transport F (𝐞 P p d) (hǫ P p (λ _ → d) (λ _ → h)) ＝ h)
             (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A)
           → apd (𝓓rec F hβ hǫ h𝐞) (𝐞 P p d) ＝
               ap (transport F (𝐞 P p d)) (𝓓rec-ǫ F hβ hǫ h𝐞 P p (λ _ → d)) ∙
                 h𝐞 P p d (𝓓rec F hβ hǫ h𝐞 d)


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
