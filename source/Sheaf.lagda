\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
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


 module _ (se : sheafification-exist) where

  open sheafification-exist se

  𝓓-nondep-rec : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                 (hβ : A → B)
                 (hǫ : (P : Ω 𝓤) → T P holds → (P holds → B) → B)
                 (h𝐞 : (P : Ω 𝓤) (p : T P holds) (b : B)
                     → hǫ P p (λ _ → b) ＝ b)
               → 𝓓 A → B
  𝓓-nondep-rec {A = A} {B} hβ hǫ h𝐞 = 𝓓rec (λ _ → B)
   hβ
   (λ P p _ → hǫ P p)
   (λ P p d b → transport-const (𝐞 P p d) ∙ h𝐞 P p b)

  𝓓-nondep-rec-β : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                   (hβ : A → B)
                   (hǫ : (P : Ω 𝓤) → T P holds → (P holds → B) → B)
                   (h𝐞 : (P : Ω 𝓤) (p : T P holds) (b : B)
                       → hǫ P p (λ _ → b) ＝ b)
                   (a : A)
                 → 𝓓-nondep-rec hβ hǫ h𝐞 (β a) ＝ hβ a
  𝓓-nondep-rec-β {A = A} {B} hβ hǫ h𝐞 = 𝓓rec-β (λ _ → B)
   hβ
   (λ P p ϕ → hǫ P p)
   (λ P p d b → transport-const (𝐞 P p d) ∙ h𝐞 P p b)

  𝓓-nondep-rec-ǫ : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                   (hβ : A → B)
                   (hǫ : (P : Ω 𝓤) → T P holds → (P holds → B) → B)
                   (h𝐞 : (P : Ω 𝓤) (p : T P holds) (b : B)
                       → hǫ P p (λ _ → b) ＝ b)
                   (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
                 → 𝓓-nondep-rec hβ hǫ h𝐞 (ǫ P p ϕ)
                    ＝ hǫ P p (λ q → 𝓓-nondep-rec hβ hǫ h𝐞 (ϕ q))
  𝓓-nondep-rec-ǫ {A = A} {B} hβ hǫ h𝐞 = 𝓓rec-ǫ (λ _ → B)
   hβ
   (λ P p ϕ → hǫ P p)
   (λ P p d b → transport-const (𝐞 P p d) ∙ h𝐞 P p b)


  -- TODO figure out if this exists in TypeTopology already
  apd-nondep : {𝓥 : Universe} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } (f : X → Y)
               {x y : X} (p : x ＝ y)
             → apd f p ＝ transport-const p ∙ ap f p
  apd-nondep f refl = refl

  transport-const-left-cancellable : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                                     {x y : A} (r : x ＝ y)
                                     {z w : B} (p q : z ＝ w)
   → transport-const r ∙ p ＝ transport-const r ∙ q
   → p ＝ q
  transport-const-left-cancellable refl p q h =
   refl-left-neutral ⁻¹ ∙ h ∙ refl-left-neutral

  transport-const-commutes : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                             {x y : A} (p : x ＝ y)
                             {z w : B} (q : z ＝ w)
   → ap (transport (λ _ → B) p) q ∙ transport-const p ＝ transport-const p ∙ q
  transport-const-commutes refl refl = refl

  𝓓-nondep-rec-𝐞 : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                   (hβ : A → B)
                   (hǫ : (P : Ω 𝓤) → T P holds → (P holds → B) → B)
                   (h𝐞 : (P : Ω 𝓤) (p : T P holds) (b : B)
                       → hǫ P p (λ _ → b) ＝ b)
                   (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A)
                 → ap (𝓓-nondep-rec hβ hǫ h𝐞) (𝐞 P p d) ＝
                    𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d) ∙
                     h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)
  𝓓-nondep-rec-𝐞 {A = A} {B} hβ hǫ h𝐞 P p d =
   transport-const-left-cancellable (𝐞 P p d) _ _
    (simplify-lhs ∙ apply-𝓓rec-𝐞 ∙ simplify-rhs)
   where
    𝓓rec-𝐞-lhs-simp = transport-const (𝐞 P p d) ∙ ap (𝓓-nondep-rec hβ hǫ h𝐞) (𝐞 P p d)

    𝓓rec-𝐞-lhs = apd (𝓓-nondep-rec hβ hǫ h𝐞) (𝐞 P p d)

    𝓓rec-𝐞-rhs =
     ap (transport (λ _ → B) (𝐞 P p d)) (𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d)) ∙
      (transport-const (𝐞 P p d) ∙
       h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d))

    𝓓rec-𝐞-rhs-simp =
     transport-const (𝐞 P p d) ∙
      (𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d) ∙
        h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d))

    simplify-lhs : 𝓓rec-𝐞-lhs-simp ＝ 𝓓rec-𝐞-lhs
    simplify-lhs = (apd-nondep (𝓓-nondep-rec hβ hǫ h𝐞) (𝐞 P p d)) ⁻¹


    apply-𝓓rec-𝐞 : 𝓓rec-𝐞-lhs ＝ 𝓓rec-𝐞-rhs
    apply-𝓓rec-𝐞 = 𝓓rec-𝐞 (λ _ → B)
          hβ
          (λ P p ϕ → hǫ P p)
          (λ P p d b → transport-const (𝐞 P p d) ∙ h𝐞 P p b) P p d

    simplify-rhs : 𝓓rec-𝐞-rhs ＝ 𝓓rec-𝐞-rhs-simp
    simplify-rhs =
     𝓓rec-𝐞-rhs
      ＝⟨ ∙assoc _ (transport-const (𝐞 P p d)) (h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)) ⁻¹ ⟩
     (ap (transport (λ _ → B) (𝐞 P p d)) (𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d)) ∙ transport-const (𝐞 P p d)) ∙ h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)
      ＝⟨ ap (_∙ h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)) (transport-const-commutes (𝐞 P p d) (𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d))) ⟩
     (transport-const (𝐞 P p d) ∙ 𝓓-nondep-rec-ǫ hβ hǫ h𝐞 P p (λ _ → d)) ∙ h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)
      ＝⟨ ∙assoc _ _ (h𝐞 P p (𝓓-nondep-rec hβ hǫ h𝐞 d)) ⟩
     𝓓rec-𝐞-rhs-simp
      ∎

  𝓓-extend : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
           → is-sheaf B → (A → B) → 𝓓 A → B
  𝓓-extend {A = A} {B} h f = 𝓓-nondep-rec f (glue h) (glue-unique h)

\end{code}

Let us consider the subobject classifier for sheaves as a study case for these
definitions of sheaves and sheafification.

In general the sheafification of Ω should not be the subobject classifier
of sheaves. This should only happen if the corresponding LT topology
preserves implication, as we will show.

\begin{code}

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

 module _ (pe : propext 𝓤) (fe : Fun-Ext) (se : sheafification-exist) where

  open sheafification-exist se

  open import UF.Logic
  open UF.Logic.Implication fe

  --ΩT-is-sheafification-implies-T-preserves-⇒ : ΩT ≃ 𝓓 (Ω 𝓤)
  --                                           → (P Q : Ω 𝓤)
  --                                           → T (P ⇒ Q) ＝ (T P ⇒ T Q)
  --ΩT-is-sheafification-implies-T-preserves-⇒ (f , _ , g , _) P Q =
  -- Ω-extensionality pe fe forwards backwards
  -- where
  --  forwards : T (P ⇒ Q) holds → (T P holds → T Q holds)
  --  forwards r p = r ≫= λ r' → p ≫= λ p' → η (r' p')

  --  backwards : (T P holds → T Q holds) → T (P ⇒ Q) holds
  --  backwards α = {!α ∘ η!}


\end{code}
