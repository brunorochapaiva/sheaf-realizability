\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Logic
open import LawvereTierney

open Conjunction

module Sheaf {𝓤 : Universe} (topology : LT-topology) where
 open LTNotation topology

 -- TODO eventually these will be added to type topology,
 -- make sure to remove them later
 apd-nondep : {𝓥 : Universe} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } (f : X → Y)
              {x y : X} (p : x ＝ y)
            → apd f p ＝ transport-const p ∙ ap f p
 apd-nondep f refl = refl

 transport-const-commutes : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
                            {x y : A} (p : x ＝ y)
                            {z w : B} (q : z ＝ w)
  → ap (transport (λ _ → B) p) q ∙ transport-const p ＝ transport-const p ∙ q
 transport-const-commutes p q =
  homotopies-are-natural _ _ (λ _ → transport-const p) {_} {_} {q} ⁻¹ ∙
  ap (transport-const p ∙_) (ap-id-is-id q)

 transport-along-＝' : {𝓥 𝓦 : Universe}
                      {A : 𝓥 ̇} {B : 𝓦 ̇}
                      (f g : A → B)
                      {x y : A} (q : x ＝ y)
                      (p : f x ＝ g x)
                   → transport (λ - → f - ＝ g -) q p ＝ ap f q ⁻¹ ∙ p ∙ ap g q
 transport-along-＝' f g refl p =
  p                            ＝⟨ refl-left-neutral ⁻¹ ⟩
  refl ∙ p                     ＝⟨ ap (_∙ p) (ap-refl f) ⟩
  ap f refl ⁻¹ ∙ p             ＝⟨ ap (ap f refl ⁻¹ ∙ p ∙_) (ap-refl g)  ⟩
  ap f refl ⁻¹ ∙ p ∙ ap g refl ∎

 ap-on-left-is-assoc : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z z' w : X} (l : x ＝ y)
                       {p : y ＝ z} {q : y ＝ z'} {r : z ＝ w} {s : z' ＝ w}
                     → p ∙ r ＝ q ∙ s
                     → (l ∙ p) ∙ r ＝ (l ∙ q) ∙ s
 ap-on-left-is-assoc l {p} {q} {r} {s} α = l ∙ p ∙ r   ＝⟨ ∙assoc l p r ⟩
                                           l ∙ (p ∙ r) ＝⟨ ap (l ∙_) α ⟩
                                           l ∙ (q ∙ s) ＝⟨ ∙assoc l q s ⁻¹ ⟩
                                           l ∙ q ∙ s   ∎

 ap-on-left-is-assoc' : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z z' : X} (l : x ＝ y)
                        (p : y ＝ z') (q : y ＝ z) (s : z ＝ z')
                      → p ＝ q ∙ s
                      → l ∙ p ＝ (l ∙ q) ∙ s
 ap-on-left-is-assoc' l p q s α = l ∙ p        ＝⟨ ap (l ∙_) α ⟩
                                  l ∙ (q ∙ s)  ＝⟨ ∙assoc l q s ⁻¹ ⟩
                                  l ∙ q ∙ s    ∎

 ap-on-left-is-assoc'' : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z z' : X} (l : x ＝ y)
                         (p : y ＝ z) (q : y ＝ z') (s : z ＝ z')
                       → p ∙ s ＝ q
                       → (l ∙ p) ∙ s ＝ l ∙ q
 ap-on-left-is-assoc'' l p q s α =
  ap-on-left-is-assoc' l q p s (α ⁻¹) ⁻¹

 ap-left-inverse : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z : X} (l : x ＝ y)
                   {p : x ＝ z} {q : y ＝ z}
                 → p ＝ l ∙ q
                 → l ⁻¹ ∙ p ＝ q
 ap-left-inverse l {p} {q} α =
  l ⁻¹ ∙ p     ＝⟨ ap-on-left-is-assoc' (l ⁻¹) p l q α ⟩
  l ⁻¹ ∙ l ∙ q ＝⟨ ap (_∙ q) (left-inverse l) ⟩
  refl ∙ q     ＝⟨ refl-left-neutral ⟩
  q            ∎

 ap-left-inverse' : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z : X} (l : x ＝ y)
                    {p : x ＝ z} {q : y ＝ z}
                  → l ⁻¹ ∙ p ＝ q
                  → p ＝ l ∙ q
 ap-left-inverse' l {p} {q} α =
  p            ＝⟨ refl-left-neutral ⁻¹ ⟩
  refl ∙ p     ＝⟨ ap (_∙ p) (sym-is-inverse' l) ⟩
  l ∙ l ⁻¹ ∙ p ＝⟨ ap-on-left-is-assoc'' l (l ⁻¹) q p α ⟩
  l ∙ q        ∎

 ap-right-inverse : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z : X} (r : y ＝ z)
                    {p : x ＝ z} {q : x ＝ y}
                  → p ＝ q ∙ r
                  → p ∙ r ⁻¹ ＝ q
 ap-right-inverse refl α = α

 ap-right-inverse' : {𝓥 : Universe} {X : 𝓥 ̇ } {x y z : X} (r : y ＝ z)
                     {p : x ＝ z} {q : x ＝ y}
                   → p ∙ r ⁻¹ ＝ q
                   → p ＝ q ∙ r
 ap-right-inverse' refl α = α

 is-sheaf : {𝓥 : Universe} → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥  ̇
 is-sheaf A =
  Σ glue ꞉ ((P : Ω 𝓤) → T P holds → (P holds → A) → A) ,
  ((P : Ω 𝓤) (p : T P holds) (x : A) → glue P p (λ _ → x) ＝ x)

 glue : {𝓥 : Universe} {A : 𝓥 ̇} → is-sheaf A → (P : Ω 𝓤) → T P holds → (P holds → A) → A
 glue = pr₁

 glue-unique : {𝓥 : Universe} {A : 𝓥 ̇} (h : is-sheaf A)
             → (P : Ω 𝓤) (p : T P holds) (x : A) → glue h P p (λ _ → x) ＝ x
 glue-unique = pr₂

 glue-natural : {𝓥 𝓦 : Universe}
              → funext 𝓤 𝓥
              → funext 𝓤 𝓦
              → {A : 𝓥 ̇} {B : 𝓦 ̇}
                (h : is-sheaf A) (j : is-sheaf B)
                (f : A → B)
                (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → A)
              → f (glue h P p ϕ) ＝ glue j P p (f ∘ ϕ)
 glue-natural fe₁ fe₂ h j f P p ϕ =
  f (glue h P p ϕ)
   ＝⟨ glue-unique j P p (f (glue h P p ϕ)) ⁻¹ ⟩
  glue j P p (λ _ → f (glue h P p ϕ))
   ＝⟨ ap (glue j P p) (dfunext fe₂ II) ⟩
  glue j P p (f ∘ ϕ) ∎
  where
   I : (i : P holds) → ϕ ∼ (λ _ → ϕ i)
   I i j = ap ϕ (holds-is-prop P j i)

   II : (λ _ → f (glue h P p ϕ)) ∼ f ∘ ϕ
   II i =
    f (glue h P p ϕ)
     ＝⟨ ap (λ g → f (glue h P p g)) (dfunext fe₁ (I i)) ⟩
    f (glue h P p (λ _ → ϕ i))
     ＝⟨ ap f (glue-unique h P p (ϕ i)) ⟩
    f (ϕ i) ∎

 glue-natural' : {𝓥 : Universe}
               → funext 𝓤 𝓥
               → {A B : 𝓥 ̇}
                 (h : is-sheaf A) (j : is-sheaf B)
                 (f : A → B)
                 (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → A)
               → f (glue h P p ϕ) ＝ glue j P p (f ∘ ϕ)
 glue-natural' fe = glue-natural fe fe

 glue-functorial-action : {𝓥 : Universe}
                        → funext 𝓤 𝓥
                        → {A : 𝓥 ̇} (h : is-sheaf A)
                          (P Q : Ω 𝓤) (p : T P holds) (f : P holds → Q holds)
                          (ϕ : Q holds → A)
                        → glue h Q (T-action f p) ϕ ＝ glue h P p (ϕ ∘ f)
 glue-functorial-action fe h P Q p f ϕ =
  glue h Q (T-action f p) ϕ
   ＝⟨ glue-unique h P p (glue h Q (T-action f p) ϕ) ⁻¹ ⟩
  glue h P p (λ i → glue h Q (T-action f p) ϕ)
   ＝⟨ ap (glue h P p) (dfunext fe II) ⟩
  glue h P p (ϕ ∘ f) ∎
  where
   I : (i : P holds) → ϕ ∼ (λ _ → ϕ (f i))
   I i j = ap ϕ (holds-is-prop Q j (f i))

   II : (λ i → glue h Q (T-action f p) ϕ) ∼ ϕ ∘ f
   II i =
    glue h Q (T-action f p) ϕ
     ＝⟨ ap (glue h Q (T-action f p)) (dfunext fe (I i)) ⟩
    glue h Q (T-action f p) (λ _ → ϕ (f i))
     ＝⟨ glue-unique h Q (T-action f p) (ϕ (f i)) ⟩
    ϕ (f i) ∎

 glue-conjunction-left : {𝓥 : Universe}
                       → funext 𝓤 𝓥
                       → {A : 𝓥 ̇} (h : is-sheaf A)
                         (P Q : Ω 𝓤)
                         (p : T P holds) (q : T Q holds)
                         (ϕ : P holds → A)
                       → glue h P p ϕ ＝ glue h (P ∧ Q) (T-pair p q) (ϕ ∘ pr₁)
 glue-conjunction-left fe h P Q p q ϕ =
  glue h P p ϕ
   ＝⟨ ap (λ α → glue h P α ϕ) (holds-is-prop (T P) p (T-action pr₁ (T-pair p q))) ⟩
  glue h P (T-action pr₁ (T-pair p q)) ϕ
   ＝⟨ glue-functorial-action fe h (P ∧ Q) P (T-pair p q) pr₁ ϕ ⟩
  glue h (P ∧ Q) (T-pair p q) (ϕ ∘ pr₁) ∎

 glue-conjunction-right : {𝓥 : Universe}
                        → funext 𝓤 𝓥
                        → {A : 𝓥 ̇} (h : is-sheaf A)
                          (P Q : Ω 𝓤)
                          (p : T P holds) (q : T Q holds)
                          (ϕ : Q holds → A)
                        → glue h Q q ϕ ＝ glue h (P ∧ Q) (T-pair p q) (ϕ ∘ pr₂)
 glue-conjunction-right fe h P Q p q ϕ =
  glue h Q q ϕ
   ＝⟨ ap (λ α → glue h Q α ϕ) (holds-is-prop (T Q) q (T-action pr₂ (T-pair p q))) ⟩
  glue h Q (T-action pr₂ (T-pair p q)) ϕ
   ＝⟨ glue-functorial-action fe h (P ∧ Q) Q (T-pair p q) pr₂ ϕ ⟩
  glue h (P ∧ Q) (T-pair p q) (ϕ ∘ pr₂) ∎

 is-sheaf-is-prop : {𝓥 : Universe}
                  → Fun-Ext
                  → {A : 𝓥 ̇}
                  → is-set A
                  → is-prop (is-sheaf A)
 is-sheaf-is-prop fe A-is-set h j = to-Σ-＝
  (dfunext fe (λ P →
    dfunext fe (λ p →
     dfunext fe (λ ϕ → glue-natural' fe h j id P p ϕ))),
   dfunext fe (λ P →
    dfunext fe (λ p →
     dfunext fe (λ x → A-is-set _ _))))

 dfunext-const : {𝓥 𝓦 : Universe}
                 (fe : funext 𝓥 𝓦)
                 {A : 𝓥  ̇} {B : 𝓦  ̇}
                 {x y : B} (p : x ＝ y)
               → dfunext fe (λ (_ : A) → p) ＝ ap (λ x _ → x) p
 dfunext-const fe {x = x} refl = dfunext-refl fe (λ _ → x) ∙ ap-refl (λ x _ → x) ⁻¹

 ap-glue-unique : {𝓥 𝓦 : Universe}
                  (fe₁ : funext 𝓤 𝓥)
                  (fe₂ : funext 𝓤 𝓦)
                  {A : 𝓥 ̇} {B : 𝓦 ̇}
                  (h : is-sheaf A) (j : is-sheaf B)
                  (f : A → B)
                  (P : Ω 𝓤) (p : T P holds) (x : A)
                →  glue-natural fe₁ fe₂ h j f P p (λ _ → x) ∙
                    glue-unique j P p (f x) ＝
                     ap f (glue-unique h P p x)
 ap-glue-unique fe₁ fe₂ h j f P p x =
  glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ aux) ∙ glue-unique j P p (f x)
   ＝⟨ I ⟩
  glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ →  ap f (glue-unique h P p x))) ∙ glue-unique j P p (f x)
   ＝⟨ II ⟩
  glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) (ap (λ x _ → x) (ap f (glue-unique h P p x))) ∙ glue-unique j P p (f x)
   ＝⟨ III ⟩
  glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) (ap (λ x _ → f x) (glue-unique h P p x)) ∙ glue-unique j P p (f x)
   ＝⟨ IV ⟩
  glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (λ a → glue j P p (λ _ → f a)) (glue-unique h P p x) ∙ glue-unique j P p (f x)
   ＝⟨ V ⟩
  ap f (glue-unique h P p x) ∎
  where
   -- auxiliary definition from glue-natural
   aux : (λ _ → f (glue h P p (λ _ → x))) ∼ (λ _ → f x)
   aux i = ap (λ g → f (glue h P p g)) (dfunext fe₁ (λ j → ap (λ _ → x) (holds-is-prop P j i))) ∙ ap f (glue-unique h P p x)

   -- in the constant family case we can simplify aux to use glue-unique
   aux-simp : aux ∼ (λ _ →  ap f (glue-unique h P p x))
   aux-simp i =
    ap (λ g → f (glue h P p g)) (dfunext fe₁ (λ j → ap (λ _ → x) (holds-is-prop P j i))) ∙ ap f (glue-unique h P p x)
     ＝⟨ I ⟩
    ap (λ g → f (glue h P p g)) (dfunext fe₁ (λ j → refl)) ∙ ap f (glue-unique h P p x)
     ＝⟨ II ⟩
    refl ∙ ap f (glue-unique h P p x)
     ＝⟨ refl-left-neutral ⟩
    ap f (glue-unique h P p x) ∎
    where
     I = ap
      (λ α → ap (λ g → f (glue h P p g)) (dfunext fe₁ α) ∙ ap f (glue-unique h P p x))
      (dfunext fe₁ (λ j → ap-const x (holds-is-prop P j i)))
     II = ap
      (λ α →  ap (λ g → f (glue h P p g)) α ∙ ap f (glue-unique h P p x))
      (dfunext-refl fe₁ _)

   I = ap
    (λ α → glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ α) ∙ glue-unique j P p (f x))
    (dfunext fe₂ aux-simp)
   II = ap
    (λ α → glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) α ∙ glue-unique j P p (f x))
    (dfunext-const fe₂ (ap f (glue-unique h P p x)))
   III = ap
    (λ α → glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ ap (glue j P p) α ∙ glue-unique j P p (f x))
    (ap-ap f (λ x _ → x) (glue-unique h P p x))
   IV = ap
    (λ α → glue-unique j P p (f (glue h P p (λ _ → x))) ⁻¹ ∙ α ∙ glue-unique j P p (f x))
    (ap-ap (λ x _ → f x) (glue j P p) (glue-unique h P p x))
   V = homotopies-are-natural'' (λ a → glue j P p (λ _ → f a)) f (glue-unique j P p ∘ f) {_} {_} {glue-unique h P p x}

 𝟙-is-sheaf : {𝓥 : Universe} → is-sheaf {𝓥} 𝟙
 𝟙-is-sheaf = (λ _ _ _ → ⋆) , (λ _ _ _ → refl)

 is-sheaf-exponentiable : {𝓥 𝓦 : Universe}
                        → funext 𝓥 𝓦
                        → {A : 𝓥 ̇} {F : A → 𝓦 ̇}
                        → ((a : A) → is-sheaf (F a))
                        → is-sheaf ((a : A) → F a)
 is-sheaf-exponentiable fe {A} {F} h =
  →-glue , λ P p f → dfunext fe (→-glue-unique P p f)
  where
   →-glue : (P : Ω 𝓤) → T P holds → (P holds → (a : A) → F a) → (a : A) → F a
   →-glue P p ϕ a = glue (h a) P p (λ i → ϕ i a)

   →-glue-unique : (P : Ω 𝓤) (p : T P holds) (f : (a : A) → F a)
                 → →-glue P p (λ _ → f) ∼ f
   →-glue-unique P p f a = glue-unique (h a) P p (f a)

 Σ-preserves-is-sheaf : {𝓥 𝓦 : Universe}
                      → funext 𝓤 𝓥
                      → funext 𝓤 𝓦
                      → {A : 𝓥 ̇} {F : A → 𝓦 ̇}
                      → is-sheaf A
                      → ((a : A) → is-sheaf (F a))
                      → is-sheaf (Σ a ꞉ A , F a)
 Σ-preserves-is-sheaf fe₁ fe₂ {A} {F} h j = Σ-glue , Σ-glue-unique
  where
   eq : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → Σ a ꞉ A , F a) (q : P holds)
      → pr₁ (ϕ q) ＝ glue h P p (λ q → pr₁ (ϕ q))
   eq P p ϕ q =
    pr₁ (ϕ q)
     ＝⟨ glue-unique h P p (pr₁ (ϕ q)) ⁻¹ ⟩
    glue h P p (λ _ → pr₁ (ϕ q))
     ＝⟨ ap (glue h P p) (dfunext fe₁ (λ r → ap (pr₁ ∘ ϕ) (holds-is-prop P q r))) ⟩
    glue h P p (λ r → pr₁ (ϕ r)) ∎

   eq-simp : (P : Ω 𝓤) (p : T P holds) (t : Σ a ꞉ A , F a) (q : P holds)
           → eq P p (λ _ → t) q ＝ glue-unique h P p (pr₁ t) ⁻¹
   eq-simp P p t q =
    glue-unique h P p (pr₁ t) ⁻¹ ∙ ap (glue h P p) (dfunext fe₁ (λ r → ap (λ _ → pr₁ t) (holds-is-prop P q r)))
     ＝⟨ ap
         (λ α → glue-unique h P p (pr₁ t) ⁻¹ ∙ ap (glue h P p) (dfunext fe₁ α))
         (dfunext fe₁ λ r → ap-const (pr₁ t) (holds-is-prop P q r)) ⟩
    glue-unique h P p (pr₁ t) ⁻¹ ∙ ap (glue h P p) (dfunext fe₁ (λ _ → refl))
     ＝⟨ ap
         (λ α → glue-unique h P p (pr₁ t) ⁻¹ ∙ ap (glue h P p) α)
         (dfunext-refl fe₁ (λ _ → pr₁ t)) ⟩
    glue-unique h P p (pr₁ t) ⁻¹ ∙ ap (glue h P p) refl
     ＝⟨ ap
         (glue-unique h P p (pr₁ t) ⁻¹ ∙_)
         (ap-refl (glue h P p)) ⟩
    glue-unique h P p (pr₁ t) ⁻¹ ∎

   Σ-glue : (P : Ω 𝓤) → T P holds → (P holds → Σ a ꞉ A , F a) → Σ a ꞉ A , F a
   Σ-glue P p ϕ = glue h P p (pr₁ ∘ ϕ)
                , glue (j (glue h P p (pr₁ ∘ ϕ))) P p
                   (λ q → transport F (eq P p ϕ q) (pr₂ (ϕ q)))

   Σ-glue-unique : (P : Ω 𝓤) (p : T P holds) (t : Σ a ꞉ A , F a)
                 → Σ-glue P p (λ _ → t) ＝ t
   Σ-glue-unique P p (a , b) = to-Σ-＝ (glue-unique h P p a , V)
    where
     I = ap
      (λ α → transport F (glue-unique h P p a) ((glue (j (glue h P p (λ _ → a))) P p α)))
      (dfunext fe₂ λ q → ap (λ α → transport F α b) (eq-simp P p (a , b) q))
     II = ap
      (transport F (glue-unique h P p a))
      (glue-natural' fe₂ (j a) (j (glue h P p (λ _ → a))) (transport F (glue-unique h P p a ⁻¹)) P p (λ _ → b) ⁻¹)
     III = back-and-forth-transport (glue-unique h P p a)
     IV = glue-unique (j a) P p b

     V =
      transport F (glue-unique h P p a) (glue (j (glue h P p (λ _ → a))) P p (λ q → transport F (eq P p (λ _ → (a , b)) q) b))
       ＝⟨ I ⟩
      transport F (glue-unique h P p a) (glue (j (glue h P p (λ _ → a))) P p (λ _ → transport F (glue-unique h P p a ⁻¹) b))
       ＝⟨ II ⟩
      transport F (glue-unique h P p a) (transport F (glue-unique h P p a ⁻¹) (glue (j a) P p (λ _ → b)))
       ＝⟨ III ⟩
      glue (j a) P p (λ _ → b)
       ＝⟨ IV ⟩
      b ∎

 ×-preserves-is-sheaf : {𝓥 𝓦 : Universe}
                      → {A : 𝓥 ̇} {B : 𝓦 ̇}
                      → is-sheaf A
                      → is-sheaf B
                      → is-sheaf (A × B)
 ×-preserves-is-sheaf {_} {_} {A} {B} h j = ×-glue , ×-glue-unique
  where
   ×-glue : (P : Ω 𝓤) → T P holds → (P holds → A × B) → A × B
   ×-glue P p ϕ = glue h P p (pr₁ ∘ ϕ) , glue j P p (pr₂ ∘ ϕ)

   ×-glue-unique : (P : Ω 𝓤) (p : T P holds) (t : A × B)
                 → ×-glue P p (λ _ → t) ＝ t
   ×-glue-unique P p t =
    ap₂ _,_ (glue-unique h P p (pr₁ t)) (glue-unique j P p (pr₂ t))

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

  𝓓-is-sheaf : {𝓥 : Universe} {A : 𝓥 ̇}
             → is-sheaf (𝓓 A)
  𝓓-is-sheaf = ǫ , 𝐞

  ap-𝐞 : {𝓥 𝓦 : Universe}
         (fe₁ : funext 𝓤 𝓥)
         (fe₂ : funext 𝓤 𝓦)
         {A : 𝓥 ̇} {B : 𝓦 ̇}
         (j : is-sheaf B) (f : 𝓓 A → B)
         (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A)
       → ap f (glue-unique 𝓓-is-sheaf P p d) ＝
          glue-natural fe₁ fe₂ 𝓓-is-sheaf j f P p (λ _ → d) ∙
           glue-unique j P p (f d)
  ap-𝐞 fe₁ fe₂ j f P p d = ap-glue-unique fe₁ fe₂ 𝓓-is-sheaf j f P p d ⁻¹

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
   cancel-left (simplify-lhs ∙ apply-𝓓rec-𝐞 ∙ simplify-rhs)
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

  𝓓-extend-β : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
               (h : is-sheaf B) (f : A → B)
               (a : A)
             → 𝓓-extend h f (β a) ＝ f a
  𝓓-extend-β h f a = 𝓓-nondep-rec-β f (glue h) (glue-unique h) a

  𝓓-extend-ǫ : {𝓥 𝓦 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇}
               (h : is-sheaf B) (f : A → B)
               (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
             → glue h P p (𝓓-extend h f ∘ ϕ) ＝ 𝓓-extend h f (ǫ P p ϕ)
  𝓓-extend-ǫ h f P p ϕ = 𝓓-nondep-rec-ǫ f (glue h) (glue-unique h) P p ϕ ⁻¹

  𝓓-extension-is-unique : {𝓥 𝓦 : Universe}
                        → funext 𝓤 𝓥
                        → funext 𝓤 𝓦
                        → {A : 𝓥 ̇} {B : 𝓦 ̇}
                        → (j : is-sheaf B) (f : A → B) (g h : 𝓓 A → B)
                        → g ∘ β ∼ f
                        → h ∘ β ∼ f
                        → g ∼ h
  𝓓-extension-is-unique fe₁ fe₂ {A} {B} j f g h H Q =
   𝓓rec (λ d → g d ＝ h d) β-case ǫ-case 𝐞-case
   where
    β-case : (a : A) → g (β a) ＝ h (β a)
    β-case a = H a ∙ Q a ⁻¹

    ǫ-case : (P : Ω 𝓤) (p : T P holds) (ϕ : P holds → 𝓓 A)
           → (g ∘ ϕ ∼ h ∘ ϕ )
           → g (ǫ P p ϕ) ＝ h (ǫ P p ϕ)
    ǫ-case P p ϕ R =
     g (ǫ P p ϕ)
      ＝⟨ glue-natural fe₁ fe₂ 𝓓-is-sheaf j g P p ϕ ⟩
     glue j P p (g ∘ ϕ)
      ＝⟨ ap (glue j P p) (dfunext fe₂ R) ⟩
     glue j P p (h ∘ ϕ)
      ＝⟨ glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p ϕ ⁻¹ ⟩
     h (ǫ P p ϕ)
      ∎

    𝐞-case : (P : Ω 𝓤) (p : T P holds) (d : 𝓓 A)
             (e : g d ＝ h d)
           → transport (λ d → g d ＝ h d) (𝐞 P p d)
              (ǫ-case P p (λ _ → d) (λ _ → e)) ＝ e
    𝐞-case P p d e =
     transport (λ d → g d ＝ h d) (𝐞 P p d) (glue-natural fe₁ fe₂ 𝓓-is-sheaf j g P p (λ _ → d) ∙ (ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹))
      ＝⟨ transport-along-＝' g h (𝐞 P p d) _ ⟩
     ap g (𝐞 P p d) ⁻¹ ∙ (glue-natural fe₁ fe₂ 𝓓-is-sheaf j g P p (λ _ → d) ∙ (ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹)) ∙ ap h (𝐞 P p d)
      ＝⟨ I ⟩
     (glue-natural fe₁ fe₂ 𝓓-is-sheaf j g P p (λ _ → d) ⁻¹ ∙ ap g (𝐞 P p d)) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ (glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹ ∙ ap h (𝐞 P p d))
      ＝⟨ II ⟩
     glue-unique j P p (g d) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ (glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹ ∙ ap h (𝐞 P p d))
      ＝⟨ III ⟩
     glue-unique j P p (g d) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ glue-unique j P p (h d)
      ＝⟨ IV ⟩
     glue-unique j P p (g d) ⁻¹ ∙ ap (glue j P p) (ap (λ x _ → x) e) ∙ glue-unique j P p (h d)
      ＝⟨ V ⟩
     glue-unique j P p (g d) ⁻¹ ∙ ap (λ x → glue j P p (λ _ → x)) e ∙ glue-unique j P p (h d)
      ＝⟨ VI ⟩
     ap id e
      ＝⟨ ap-id-is-id e ⟩
     e ∎
     where
      rearrange : {x1 x2 x3 x4 x5 x6 : B}
          (p : x2 ＝ x1) (q : x2 ＝ x3) (r : x3 ＝ x4) (s : x4 ＝ x5) (t : x5 ＝ x6)
        → p ⁻¹ ∙ (q ∙ (r ∙ s)) ∙ t ＝ (q ⁻¹ ∙ p) ⁻¹ ∙ r ∙ (s ∙ t)
      rearrange p q r s t =
       p ⁻¹ ∙ (q ∙ (r ∙ s)) ∙ t     ＝⟨ ap (_∙ t) (∙assoc (p ⁻¹) q (r ∙ s) ⁻¹) ⟩
       p ⁻¹ ∙ q ∙ (r ∙ s) ∙ t       ＝⟨ ∙assoc (p ⁻¹ ∙ q) (r ∙ s) t  ⟩
       p ⁻¹ ∙ q ∙ ((r ∙ s) ∙ t)     ＝⟨ ap (p ⁻¹ ∙ q ∙_) (∙assoc r s t) ⟩
       p ⁻¹ ∙ q ∙ (r ∙ (s ∙ t))     ＝⟨ ∙assoc ((p ⁻¹ ∙ q)) r (s ∙ t) ⁻¹ ⟩
       p ⁻¹ ∙ q ∙ r ∙ (s ∙ t)       ＝⟨ ap (λ α → (p ⁻¹ ∙ α) ∙ r ∙ (s ∙ t)) (⁻¹-involutive q ⁻¹) ⟩
       p ⁻¹ ∙ q ⁻¹ ⁻¹ ∙ r ∙ (s ∙ t) ＝⟨ ap (λ α → α ∙ r ∙ (s ∙ t)) (⁻¹-contravariant (q ⁻¹) p) ⟩
       (q ⁻¹ ∙ p) ⁻¹ ∙ r ∙ (s ∙ t)  ∎

      I = rearrange
           (ap g (𝐞 P p d))
           (glue-natural fe₁ fe₂ 𝓓-is-sheaf j g P p (λ _ → d))
           (ap (glue j P p) (dfunext fe₂ (λ _ → e)))
           (glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹)
           (ap h (𝐞 P p d))
      II = ap
       (λ α → α ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ (glue-natural fe₁ fe₂ 𝓓-is-sheaf j h P p (λ _ → d) ⁻¹ ∙ ap h (𝐞 P p d)))
       (ap-left-inverse _ {_} {glue-unique j P p (g d)} (ap-glue-unique fe₁ fe₂ 𝓓-is-sheaf j g P p d ⁻¹))
      III = ap
       (λ α → glue-unique j P p (g d) ⁻¹ ∙ ap (glue j P p) (dfunext fe₂ (λ _ → e)) ∙ α)
       (ap-left-inverse _ {_} {glue-unique j P p (h d)} (ap-glue-unique fe₁ fe₂ 𝓓-is-sheaf j h P p d ⁻¹))
      IV = ap
       (λ α → glue-unique j P p (g d) ⁻¹ ∙ ap (glue j P p) α ∙ glue-unique j P p (h d))
       (dfunext-const fe₂ e)
      V = ap
       (λ α → glue-unique j P p (g d) ⁻¹ ∙ α ∙ glue-unique j P p (h d))
       (ap-ap (λ x _ → x) (glue j P p) e)
      VI = homotopies-are-natural'' (λ x → glue j P p (λ _ → x)) id (glue-unique j P p) {_} {_} {e}

  𝓓-extend-unique : {𝓥 𝓦 : Universe}
                  → funext 𝓤 𝓥
                  → funext 𝓤 𝓦
                  → {A : 𝓥 ̇} {B : 𝓦 ̇}
                  → (j : is-sheaf B) (f : A → B) (g : 𝓓 A → B)
                  → g ∘ β ∼ f
                  → g ∼ 𝓓-extend j f
  𝓓-extend-unique fe₁ fe₂ j f g H =
   𝓓-extension-is-unique fe₁ fe₂ j f g (𝓓-extend j f) H (𝓓-extend-β j f)

  𝓓-extend₂ : {𝓥 𝓦 𝓧 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇} {C : 𝓧 ̇}
            → funext 𝓦 𝓧
            → is-sheaf C
            → (A → B → C)
            → 𝓓 A → 𝓓 B → C
  𝓓-extend₂ fe h f = 𝓓-extend
   (is-sheaf-exponentiable fe λ _ → h)
   (λ a → 𝓓-extend h (f a))

  𝓓-extend₂-β : {𝓥 𝓦 𝓧 : Universe} {A : 𝓥 ̇} {B : 𝓦 ̇} {C : 𝓧 ̇}
                 (fe : funext 𝓦 𝓧)
                 (h : is-sheaf C)
                 (f : A → B → C)
                 (a : A) (b : B)
               → 𝓓-extend₂ fe h f (β a) (β b) ＝ f a b
  𝓓-extend₂-β fe h f a b =
   𝓓-extend (is-sheaf-exponentiable fe λ _ → h) (λ a → 𝓓-extend h (f a)) (β a) (β b)
    ＝⟨ ap (λ α → α (β b))
          (𝓓-extend-β (is-sheaf-exponentiable fe λ _ → h) (λ a → 𝓓-extend h (f a)) a) ⟩
   𝓓-extend h (f a) (β b)
    ＝⟨ 𝓓-extend-β h (f a) b ⟩
   f a b ∎

  𝓓-extend₂-unique : {𝓥 𝓦 𝓧 : Universe}
                     (fe : Fun-Ext)
                     {A : 𝓥 ̇} {B : 𝓦 ̇} {C : 𝓧 ̇}
                     (j : is-sheaf C) (f : A → B → C) (g : 𝓓 A → 𝓓 B → C)
                   → ((a : A) (b : B) → g (β a) (β b) ＝ f a b)
                   → (d₁ : 𝓓 A) (d₂ : 𝓓 B)
                   → g d₁ d₂ ＝ 𝓓-extend₂ fe j f d₁ d₂
  𝓓-extend₂-unique fe j f g H d₁ d₂ = ap (λ α → α d₂)
   (𝓓-extend-unique fe fe
     (is-sheaf-exponentiable fe λ _ → j)
     (λ a → 𝓓-extend j (f a))
     g
     (λ a → dfunext fe (𝓓-extend-unique fe fe j (f a) (g (β a)) (H a)))
     d₁)

  𝓓-extension₂-is-unique : {𝓥 𝓦 𝓧 : Universe}
                           (fe : Fun-Ext)
                           {A : 𝓥 ̇} {B : 𝓦 ̇} {C : 𝓧 ̇}
                           (j : is-sheaf C) (f : A → B → C) (g h : 𝓓 A → 𝓓 B → C)
                         → ((a : A) (b : B) → g (β a) (β b) ＝ f a b)
                         → ((a : A) (b : B) → h (β a) (β b) ＝ f a b)
                         → (d₁ : 𝓓 A) (d₂ : 𝓓 B)
                         → g d₁ d₂ ＝ h d₁ d₂
  𝓓-extension₂-is-unique fe j f g h H I d₁ d₂ =
   𝓓-extend₂-unique fe j f g H d₁ d₂ ∙ 𝓓-extend₂-unique fe j f h I d₁ d₂ ⁻¹

  𝓓-is-identity-on-sheaves : {𝓥 : Universe}
                           → funext 𝓤 𝓥
                           → {A : 𝓥 ̇}
                           → is-sheaf A
                           → 𝓓 A ≅ A
  𝓓-is-identity-on-sheaves fe h = 𝓓-extend h id , β , fg , gf
   where
    fg : β ∘ 𝓓-extend h id ∼ id
    fg = 𝓓-extension-is-unique fe fe 𝓓-is-sheaf β (β ∘ 𝓓-extend h id) id
     (λ d → ap β (𝓓-nondep-rec-β id (glue h) (glue-unique h) d))
     (λ d → refl)

    gf : 𝓓-extend h id ∘ β ∼ id
    gf = 𝓓-nondep-rec-β id (glue h) (glue-unique h)

  𝓓-is-idempotent : {𝓥 : Universe}
                  → funext 𝓤 𝓥
                  → {A : 𝓥 ̇}
                  → 𝓓 (𝓓 A) ≅ 𝓓 A
  𝓓-is-idempotent fe = 𝓓-is-identity-on-sheaves fe 𝓓-is-sheaf

  𝓓-preserves-products : {𝓥 𝓦 : Universe}
                       → Fun-Ext
                       → {A : 𝓥 ̇} {B : 𝓦 ̇}
                       → 𝓓 A × 𝓓 B ≅ 𝓓 (A × B)
  𝓓-preserves-products fe {A} {B} = f , g , gf , fg
   where
    f : 𝓓 A × 𝓓 B → 𝓓 (A × B)
    f (da , db) = 𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) da db

    g : 𝓓 (A × B) → 𝓓 A × 𝓓 B
    g d = 𝓓-extend 𝓓-is-sheaf (β ∘ pr₁) d , 𝓓-extend 𝓓-is-sheaf (β ∘ pr₂) d

    gfβ₁ : (a : A) (b : B)
         → 𝓓-extend 𝓓-is-sheaf (β ∘ pr₁)
            (𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) (β a) (β b)) ＝ β a
    gfβ₁ a b =
     𝓓-extend 𝓓-is-sheaf (β ∘ pr₁)
      (𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) (β a) (β b))
      ＝⟨ ap (𝓓-extend 𝓓-is-sheaf (β ∘ pr₁))
            (𝓓-extend₂-β fe 𝓓-is-sheaf (λ a b → β (a , b)) a b) ⟩
     𝓓-extend 𝓓-is-sheaf (β ∘ pr₁) (β (a , b))
      ＝⟨ 𝓓-extend-β 𝓓-is-sheaf (β ∘ pr₁) (a , b) ⟩
     β a ∎

    gfβ₂ : (a : A) (b : B)
         → 𝓓-extend 𝓓-is-sheaf (β ∘ pr₂)
            (𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) (β a) (β b)) ＝ β b
    gfβ₂ a b =
     𝓓-extend 𝓓-is-sheaf (β ∘ pr₂)
      (𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) (β a) (β b))
      ＝⟨ ap (𝓓-extend 𝓓-is-sheaf (β ∘ pr₂))
            (𝓓-extend₂-β fe 𝓓-is-sheaf (λ a b → β (a , b)) a b) ⟩
     𝓓-extend 𝓓-is-sheaf (β ∘ pr₂) (β (a , b))
      ＝⟨ 𝓓-extend-β 𝓓-is-sheaf (β ∘ pr₂) (a , b) ⟩
     β b ∎

    gf : g ∘ f ∼ id
    gf (da , db) = 𝓓-extension₂-is-unique
     fe
     (×-preserves-is-sheaf 𝓓-is-sheaf 𝓓-is-sheaf)
     (λ a b → (β a , β b))
     (λ a b → g (f (a , b)))
     _,_
     (λ a b → ap₂ _,_ (gfβ₁ a b) (gfβ₂ a b))
     (λ a b → refl)
     da
     db

    fgβ : f ∘ g ∘ β ∼ β
    fgβ (a , b) =
     𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b))
      (𝓓-extend 𝓓-is-sheaf (β ∘ pr₁) (β (a , b)))
      (𝓓-extend 𝓓-is-sheaf (β ∘ pr₂) (β (a , b)))
       ＝⟨ ap₂ (𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)))
              (𝓓-extend-β 𝓓-is-sheaf (β ∘ pr₁) (a , b))
              (𝓓-extend-β 𝓓-is-sheaf (β ∘ pr₂) (a , b)) ⟩
     𝓓-extend₂ fe 𝓓-is-sheaf (λ a b → β (a , b)) (β a) (β b)
      ＝⟨ 𝓓-extend₂-β fe 𝓓-is-sheaf (λ a b → β (a , b)) a b ⟩
     β (a , b) ∎

    fg : f ∘ g ∼ id
    fg = 𝓓-extension-is-unique fe fe 𝓓-is-sheaf β (f ∘ g) id fgβ (λ t → refl)

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
   ΩT-glue P _ f = R , R-is-T-stable
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
   ΩT-glue-unique P p (Q , Q-is-T-stable) = ΩT-extensionality pe fe forward backward
    where
     forward : (P holds → Q holds) → Q holds
     forward f = Q-is-T-stable (p ≫= (η ∘ f))

     backward : Q holds → (P holds → Q holds)
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
