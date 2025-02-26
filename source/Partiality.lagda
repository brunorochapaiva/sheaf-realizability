\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt using (funext)
open import UF.Lower-FunExt using (lower-funext)
open import UF.Sets using (is-set)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module Partiality (𝓣 : Universe) where

 open import Lifting.Construction 𝓣 public
 open import Lifting.Monad 𝓣 public
 open import Lifting.UnivalentPrecategory 𝓣
 open import Lifting.Miscelanea 𝓣

 binary-Kleisli : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                → (X → Y → 𝓛 Z)
                → 𝓛 X → 𝓛 Y → 𝓛 Z
 binary-Kleisli f x y =
  (Σ ϕ ꞉ is-defined x , Σ ψ ꞉ is-defined y , is-defined (f (value x ϕ) (value y ψ))) ,
  (λ (ϕ , ψ , χ) → value (f (value x ϕ) (value y ψ)) χ) ,
  Σ-is-prop (being-defined-is-prop x) λ ϕ →
   Σ-is-prop (being-defined-is-prop y) λ ψ →
    being-defined-is-prop (f (value x ϕ) (value y ψ))

 binary-Kleisli-is-defined-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                                → (f : X → Y → 𝓛 Z)
                                → (x : 𝓛 X) (y : 𝓛 Y)
                                → is-defined (binary-Kleisli f x y)
                                → is-defined x
 binary-Kleisli-is-defined-left _ _ _ (h , _) = h

 binary-Kleisli-is-defined-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                                → (f : X → Y → 𝓛 Z)
                                → (x : 𝓛 X) (y : 𝓛 Y)
                                → is-defined (binary-Kleisli f x y)
                                → is-defined y
 binary-Kleisli-is-defined-right _ _ _ (_ , h , _) = h

 _! : {X : 𝓤 ̇} → 𝓛 X → Ω 𝓣
 _! x = is-defined x , being-defined-is-prop x

 infix 5 _!

 _≡_ : {X : 𝓤 ̇} → 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
 x ≡ y = Σ i ꞉ is-defined x , Σ j ꞉ is-defined y , value x i ＝ value y j

 _≼_ : {X : 𝓤 ̇} → 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
 _≼_ {𝓤} {X} = _⊑_ {𝓤} X

 _≋_ : {X : 𝓤 ̇} → 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
 x ≋ y = x ≼ y × y ≼ x

 infix 5 _≡_
 infix 5 _≼_
 infix 5 _≋_

 ≡-symm : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → y ≡ x
 ≡-symm x y (h , j , eq) = j , h , (eq ⁻¹)

 ≡-trans : {X : 𝓤 ̇} → (x y z : 𝓛 X) → x ≡ y → y ≡ z → x ≡ z
 ≡-trans x y z (h , j , e) (k , l , f) = h , l , eq
  where
   eq = value x h ＝⟨ e ⟩
        value y j ＝⟨ ap (value y) (being-defined-is-prop y j k) ⟩
        value y k ＝⟨ f ⟩
        value z l ∎

 ≡-is-defined-left : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → is-defined x
 ≡-is-defined-left _ _ (h , _) = h

 ≡-is-defined-right : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → is-defined y
 ≡-is-defined-right _ _ (_ , h , _) = h

 ≡-value : {X : 𝓤 ̇} → (x y : 𝓛 X) (h : is-defined x) (j : is-defined y)
         → x ≡ y → value x h ＝ value y j
 ≡-value x y h j (k , l , e) =
  value x h ＝⟨ ap (value x) (being-defined-is-prop x h k) ⟩
  value x k ＝⟨ e ⟩
  value y l ＝⟨ ap (value y) (being-defined-is-prop y l j) ⟩
  value y j ∎

 ≡-implies-≼ : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → x ≼ y
 ≡-implies-≼ x y (h , i , j) = (λ _ → i) , λ l → ≡-value x y l i (h , i , j)

 ≼-refl : {X : 𝓤 ̇} (x : 𝓛 X) → x ≼ x
 ≼-refl x = id , (λ _ → refl)

 ≼-trans : {X : 𝓤 ̇} (x y z : 𝓛 X) → x ≼ y → y ≼ z → x ≼ z
 ≼-trans {𝓤} {X} x y z h j = 𝓛-comp {𝓤} X x y z h j

 ≼-preserves-defined : {X : 𝓤 ̇} (x y : 𝓛 X)
                     → x ≼ y → is-defined x → is-defined y
 ≼-preserves-defined {𝓤} {X} = def-pr {𝓤} X

 ≼-value : {X : 𝓤 ̇} → (x y : 𝓛 X) (h : is-defined x) (j : is-defined y)
         → x ≼ y → value x h ＝ value y j
 ≼-value x y h i (f , δ) = ≡-value x y h i (h , f h , δ h)

 is-defined-≼-implies-≡ : {X : 𝓤 ̇} (x y : 𝓛 X)
                        → is-defined x
                        → x ≼ y
                        → x ≡ y
 is-defined-≼-implies-≡ x y ϕ (g , δ) = ϕ , g ϕ , δ ϕ

 𝓛̇-≼ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (x y : 𝓛 X)
     → x ≼ y → 𝓛̇ f x ≼ 𝓛̇ f y
 𝓛̇-≼ f x y (g , δ) = g , λ ϕ → ap f (δ ϕ)

 ≼-ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓛 Y) (x y : 𝓛 X) → x ≼ y → (f ♯) x ≼ (f ♯) y
 ≼-ap f x y (g , δ) = h , ϵ
  where
   h : is-defined ((f ♯) x) → is-defined ((f ♯) y)
   h (ϕ , ψ) = g ϕ , transport (is-defined ∘ f) (δ ϕ) ψ

   ϵ : value ((f ♯) x) ∼ value ((f ♯) y) ∘ h
   ϵ (ϕ , ψ) = ≡-value (f (value x ϕ)) (f (value y (g ϕ)))
    ψ
    (transport (is-defined ∘ f) (δ ϕ) ψ)
    (transport (f (value x ϕ) ≡_) (ap f (δ ϕ)) (ψ , ψ , refl))

 binary-Kleisli-≼ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
         (x₁ x₂ : 𝓛 X) (y₁ y₂ : 𝓛 Y)
         (f : X → Y → 𝓛 Z)
       → x₁ ≼ x₂ → y₁ ≼ y₂ → binary-Kleisli f x₁ y₁ ≼ binary-Kleisli f x₂ y₂
 binary-Kleisli-≼ x₁ x₂ y₁ y₂ f (g , δ) (h , ϵ) = i , γ
  where
   i : is-defined (binary-Kleisli f x₁ y₁) → is-defined (binary-Kleisli f x₂ y₂)
   i (ϕ , ψ , χ) = g ϕ , h ψ , transport is-defined (ap₂ f (δ ϕ) (ϵ ψ)) χ

   γ : value (binary-Kleisli f x₁ y₁) ∼ value (binary-Kleisli f x₂ y₂) ∘ i
   γ (ϕ , ψ , χ) = ≡-value
     (f (value x₁ ϕ) (value y₁ ψ))
     (f (value x₂ (g ϕ)) (value y₂ (h ψ)))
     χ
     ξ
     (transport (f (value x₁ ϕ) (value y₁ ψ) ≡_) (ap₂ f (δ ϕ) (ϵ ψ)) (χ , χ , refl))
    where
     ξ : is-defined (f (value x₂ (g ϕ)) (value y₂ (h ψ)))
     ξ = transport is-defined (ap₂ f (δ ϕ) (ϵ ψ)) χ

 binary-Kleisli-≼-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                         (x₁ x₂ : 𝓛 X) (y : 𝓛 Y)
                         (f : X → Y → 𝓛 Z)
                       → x₁ ≼ x₂
                       → binary-Kleisli f x₁ y ≼ binary-Kleisli f x₂ y
 binary-Kleisli-≼-left x₁ x₂ y f h = binary-Kleisli-≼ x₁ x₂ y y f h (≼-refl y)

 binary-Kleisli-≼-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                          (x : 𝓛 X) (y₁ y₂ : 𝓛 Y)
                          (f : X → Y → 𝓛 Z)
                        → y₁ ≼ y₂
                        → binary-Kleisli f x y₁ ≼ binary-Kleisli f x y₂
 binary-Kleisli-≼-right x y₁ y₂ f h = binary-Kleisli-≼ x x y₁ y₂ f (≼-refl x) h

 ≋-preserves-is-defined : {X : 𝓤 ̇} (x y : 𝓛 X)
                        → x ≋ y → is-defined x → is-defined y
 ≋-preserves-is-defined x y h = ≼-preserves-defined x y (pr₁ h)

 module _ {X : 𝓤 ̇} (X-is-set : is-set X) where

  ≡-is-prop : (x y : 𝓛 X) → is-prop (x ≡ y)
  ≡-is-prop x y = Σ-is-prop (being-defined-is-prop x)
                   λ _ → Σ-is-prop (being-defined-is-prop y)
                    λ _ → X-is-set

  ≼-is-prop : (fe : funext 𝓣 (𝓤 ⊔ 𝓣))
              (x y : 𝓛 X) → is-prop (x ≼ y)
  ≼-is-prop fe x y = Σ-is-prop (Π-is-prop (lower-funext 𝓣 𝓤 fe) λ _ → being-defined-is-prop y)
                      λ _ → Π-is-prop (lower-funext 𝓣 𝓣 fe)
                       λ _ → X-is-set

  ≋-is-prop : (fe : funext 𝓣 (𝓤 ⊔ 𝓣))
              (x y : 𝓛 X) → is-prop (x ≋ y)
  ≋-is-prop fe x y = Σ-is-prop (≼-is-prop fe x y) (λ _ → ≼-is-prop fe y x)

 binary-Kleisli-η-both : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                       → (f : X → Y → 𝓛 Z)
                       → (x : X) (y : Y)
                       → binary-Kleisli f (η x) (η y) ≋ f x y
 binary-Kleisli-η-both f x y = left , right
  where
   left : binary-Kleisli f (η x) (η y) ≼ f x y
   left = (λ (⋆ , ⋆ , ϕ) → ϕ) , λ _ → refl

   right : f x y ≼ binary-Kleisli f (η x) (η y)
   right = (λ ϕ → ⋆ , ⋆ , ϕ) , λ _ → refl

\end{code}
