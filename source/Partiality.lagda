\begin{code}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module Partiality (𝓣 : Universe) where

 open import Lifting.Construction 𝓣 public
 open import Lifting.Monad 𝓣 public

 binary-Kleisli : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                → (X → Y → 𝓛 Z)
                → 𝓛 X → 𝓛 Y → 𝓛 Z
 binary-Kleisli f x y = μ (𝓛̇ (λ g → (g ♯) y) (𝓛̇ f x))

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
 x ≼ y = is-defined x → x ≡ y

 _≋_ : {X : 𝓤 ̇} → 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
 x ≋ y = x ≼ y × y ≼ x

 infix 5 _≡_
 infix 5 _≼_
 infix 5 _≋_

 ≡-is-defined-left : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → is-defined x
 ≡-is-defined-left _ _ (h , _) = h

 ≡-is-defined-right : {X : 𝓤 ̇} → (x y : 𝓛 X) → x ≡ y → is-defined y
 ≡-is-defined-right _ _ (_ , h , _) = h

 module _ {X : 𝓤 ̇} (X-is-set : is-set X) where

  ≡-is-prop : (x y : 𝓛 X) → is-prop (x ≡ y)
  ≡-is-prop x y = Σ-is-prop (being-defined-is-prop x)
                   λ _ → Σ-is-prop (being-defined-is-prop y)
                    λ _ → X-is-set

  ≼-is-prop : (fe : funext 𝓣 (𝓣 ⊔ 𝓤))
              (x y : 𝓛 X) → is-prop (x ≼ y)
  ≼-is-prop fe x y = Π-is-prop fe (λ _ → ≡-is-prop x y)

  ≋-is-prop : (fe : funext 𝓣 (𝓣 ⊔ 𝓤))
              (x y : 𝓛 X) → is-prop (x ≋ y)
  ≋-is-prop fe x y = Σ-is-prop (≼-is-prop fe x y) (λ _ → ≼-is-prop fe y x)

\end{code}
