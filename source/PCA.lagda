\begin{code}

open import MLTT.Spartan
open import PAS
open import Polynomial

module PCA {𝓣 𝓤 : Universe} where

 -- Partial combinatory algebra structure
 PCA-structure : (𝒜 : PAS 𝓣 𝓤) → 𝓤 ⊔ 𝓣 ̇
 PCA-structure 𝒜 = Σ 𝕜 ꞉ ⟅ 𝒜 ⟆ , Σ 𝕤 ꞉ A ,
    ((a b : A) → ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 b ⟧ ≡ η a)
  × ((a b : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b ⟧)
  × ((a b c : A) → ⟦ 𝕔 a · 𝕔 c · (𝕔 b · 𝕔 c) ⟧ ≼ ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b · 𝕔 c  ⟧)
  where
   open import Partiality 𝓣
   open PASNotation 𝒜
   open PolynomialNotation 𝒜

 module _ {𝒜 : PAS 𝓣 𝓤} where

  open import Partiality 𝓣
  open PASNotation 𝒜
  open PolynomialNotation 𝒜

  𝕜[_] : PCA-structure 𝒜 → A
  𝕜[ pca ] = pr₁ pca

  𝕤[_] : PCA-structure 𝒜 → A
  𝕤[ pca ] = pr₁ (pr₂ pca)

  k-law₁ : (pca : PCA-structure 𝒜)
         → (a b : A)
         → ⟦ 𝕔 𝕜[ pca ] · 𝕔 a · 𝕔 b ⟧ ≡ η a
  k-law₁ pca = pr₁ (pr₂ (pr₂ pca))

  k-law₀ : (pca : PCA-structure 𝒜)
         → (a : A)
         → is-defined (⟦ 𝕔 𝕜[ pca ] · 𝕔 a ⟧)
  k-law₀ pca a = ·-is-defined-left 𝒜 (𝕔 𝕜[ pca ] · 𝕔 a) (𝕔 𝕜[ pca ])
   (≡-is-defined-left ⟦ 𝕔 𝕜[ pca ] · 𝕔 a · 𝕔 𝕜[ pca ] ⟧ (η a) (k-law₁ pca a 𝕜[ pca ]))

  s-law₁ : (pca : PCA-structure 𝒜)
         → (a b : A)
         → is-defined ⟦ 𝕔 𝕤[ pca ] · 𝕔 a · 𝕔 b ⟧
  s-law₁ pca = pr₁ (pr₂ (pr₂ (pr₂ pca)))

  s-law₀ : (pca : PCA-structure 𝒜)
         → (a : A)
         → is-defined ⟦ 𝕔 𝕤[ pca ] · 𝕔 a  ⟧
  s-law₀ pca a = ·-is-defined-left 𝒜 (𝕔 𝕤[ pca ] · 𝕔 a) (𝕔 𝕜[ pca ]) (s-law₁ pca a 𝕜[ pca ])

  s-law₂ : (pca : PCA-structure 𝒜)
         → (a b c : A)
         → ⟦ 𝕔 a · 𝕔 c · (𝕔 b · 𝕔 c) ⟧
           ≼ ⟦ 𝕔 𝕤[ pca ] · 𝕔 a · 𝕔 b · 𝕔 c  ⟧
  s-law₂ pca = pr₂ (pr₂ (pr₂ (pr₂  pca)))

  k-law₁' : (pca : PCA-structure 𝒜)
          → (a b : A)
          → η a ≼ ⟦ 𝕔 𝕜[ pca ] · 𝕔 a · 𝕔 b ⟧
  k-law₁' pca a b = ≡-implies-≼ (η a) ⟦ 𝕔 𝕜[ pca ] · 𝕔 a · 𝕔 b ⟧
   (≡-symm ⟦ 𝕔 𝕜[ pca ] · 𝕔 a · 𝕔 b ⟧ (η a) (k-law₁ pca a b))

  --p-k-law₀ : (pca : PCA-structure 𝒜)
  --         → (t : Poly 𝒜 0)
  --         → is-defined ⟦ 𝕔 𝕜[ pca ] · t ⟧
  --p-k-law₀ pca t = {!!}

  p-k-law₁ : (pca : PCA-structure 𝒜)
           → (t r : Poly 𝒜 0)
           → is-defined ⟦ r ⟧
           → ⟦ t ⟧ ≼ ⟦ 𝕔 𝕜[ pca ] · t · r ⟧
  p-k-law₁ pca t r ψ = {!!} , {!!}
   where
    f : is-defined ⟦ t ⟧ → is-defined ⟦ 𝕔 𝕜[ pca ] · t · r ⟧
    f ϕ = (⋆ , ϕ , χ) , ψ , ξ
     where
      χ' : is-defined (binary-Kleisli _⊕_ (η 𝕜[ pca ]) (η (value (evaluate 𝒜 t) ϕ)))
      χ' = k-law₀ pca (value (evaluate 𝒜 t) ϕ)

      χ : is-defined (𝕜[ pca ] ⊕ value (evaluate 𝒜 t) ϕ)
      χ = ≋-preserves-is-defined
       (binary-Kleisli _⊕_ (η 𝕜[ pca ]) (η (value (evaluate 𝒜 t) ϕ)))
       (𝕜[ pca ] ⊕ value (evaluate 𝒜 t) ϕ)
       (binary-Kleisli-η-both _⊕_ 𝕜[ pca ] (value (evaluate 𝒜 t) ϕ))
       χ'

      ξ' : is-defined (binary-Kleisli
            _⊕_
            (η (value (𝕜[ pca ] ⊕ value (evaluate 𝒜 t) ϕ) χ))
            (η (value (evaluate 𝒜 r) ψ)))
      ξ' = ≋-preserves-is-defined
       {!!}
       {!!}
       {!!}
       {!!}

      ξ : is-defined (value (𝕜[ pca ] ⊕ value (evaluate 𝒜 t) ϕ) χ ⊕ value (evaluate 𝒜 r) ψ)
      ξ = {!!}
       where
        I : is-defined (binary-Kleisli
                         _⊕_
                         (binary-Kleisli
                          _⊕_
                          (η 𝕜[ pca ])
                          (η (value (evaluate 𝒜 t) ϕ)))
                         (η (value (evaluate 𝒜 r) ψ)))
        I = ≡-is-defined-left
         ⟦ 𝕔 𝕜[ pca ] · 𝕔 (value (evaluate 𝒜 t) ϕ) · 𝕔 (value (evaluate 𝒜 r) ψ) ⟧
         (η _)
         (k-law₁ pca (value (evaluate 𝒜 t) ϕ) (value (evaluate 𝒜 r) ψ))


  module PCAStructureNotation (pca : PCA-structure 𝒜) where

   𝕜 : A
   𝕜 = 𝕜[ pca ]

   𝕤 : A
   𝕤 = 𝕤[ pca ]


\end{code}
 PCA : (𝓣 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓣 ⁺  ̇
 PCA 𝓣 𝓤 = Σ (PCA-structure {𝓣} {𝓤})

 module _ {𝓣 𝓤 : Universe} where

  open import Partiality 𝓣

  〖_〗 : PCA 𝓣 𝓤 → PAS 𝓣 𝓤
  〖_〗 = pr₁

  【_】 : (𝔸 : PCA 𝓣 𝓤) → PCA-structure 〖 𝔸 〗
  【_】 = pr₂

  𝕜[_] : (𝔸 : PCA 𝓣 𝓤) → ⟅ 〖 𝔸 〗 ⟆
  𝕜[ 𝔸 ] = pr₁ 【 𝔸 】

  𝕤[_] : (𝔸 : PCA 𝓣 𝓤) → ⟅ 〖 𝔸 〗 ⟆
  𝕤[ 𝔸 ] = pr₁ (pr₂ 【 𝔸 】)

  evaluate' : (𝔸 : PCA 𝓣 𝓤) → Poly 〖 𝔸 〗 0 → 𝓛 ⟅ 〖 𝔸 〗 ⟆
  evaluate' 𝔸 = evaluate 〖 𝔸 〗

  syntax evaluate' 𝔸 t = ⟦ t ⟧〖 𝔸 〗

  k-law₁ : (𝔸 : PCA 𝓣 𝓤)
         → (a b : ⟅ 〖 𝔸 〗 ⟆)
         → ⟦ 𝕔 𝕜[ 𝔸 ] · 𝕔 a · 𝕔 b ⟧〖 𝔸 〗 ≡ η a
  k-law₁ 𝔸 = pr₁ (pr₂ (pr₂ (pr₂ 𝔸)))

  k-law₀ : (𝔸 : PCA 𝓣 𝓤)
         → (a : ⟅ 〖 𝔸 〗 ⟆)
         → is-defined (⟦ 𝕔 𝕜[ 𝔸 ] · 𝕔 a ⟧〖 𝔸 〗)
  k-law₀ 𝔸 a = ·-is-defined-left 〖 𝔸 〗 (𝕔 𝕜[ 𝔸 ] · 𝕔 a) (𝕔 𝕜[ 𝔸 ])
   (≡-is-defined-left ⟦ 𝕔 𝕜[ 𝔸 ] · 𝕔 a · 𝕔 𝕜[ 𝔸 ] ⟧〖 𝔸 〗 (η a) (k-law₁ 𝔸 a 𝕜[ 𝔸 ]))

  s-law₁ : (𝔸 : PCA 𝓣 𝓤)
         → (a b : ⟅ 〖 𝔸 〗 ⟆)
         → is-defined ⟦ 𝕔 𝕤[ 𝔸 ] · 𝕔 a · 𝕔 b ⟧〖 𝔸 〗
  s-law₁ 𝔸 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))

  s-law₀ : (𝔸 : PCA 𝓣 𝓤)
         → (a : ⟅ 〖 𝔸 〗 ⟆)
         → is-defined ⟦ 𝕔 𝕤[ 𝔸 ] · 𝕔 a  ⟧[ 〖 𝔸 〗 ]
  s-law₀ 𝔸 a = ·-is-defined-left 〖 𝔸 〗 (𝕔 𝕤[ 𝔸 ] · 𝕔 a) (𝕔 𝕜[ 𝔸 ]) (s-law₁ 𝔸 a 𝕜[ 𝔸 ])

  s-law₂ : (𝔸 : PCA 𝓣 𝓤)
         → (a b c : ⟅ 〖 𝔸 〗 ⟆)
         → ⟦ 𝕔 a · 𝕔 c · (𝕔 b · 𝕔 c) ⟧[ 〖 𝔸 〗 ]
           ≼ ⟦ 𝕔 𝕤[ 𝔸 ] · 𝕔 a · 𝕔 b · 𝕔 c  ⟧[ 〖 𝔸 〗 ]
  s-law₂ 𝔸 = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))

 module PCANotation {𝓣 𝓤 : Universe } (𝔸 : PCA 𝓣 𝓤) where

  open import Polynomial
  open import Partiality 𝓣

  𝒜 : PAS 𝓣 𝓤
  𝒜 = 〖 𝔸 〗

  open PASNotation 𝒜
  open PolynomialNotation 𝒜

  𝕜 : A
  𝕜 = 𝕜[ 𝔸 ]

  𝕤 : A
  𝕤 = 𝕤[ 𝔸 ]

  k-law₁' : (a b : A) → ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 b ⟧ ≡ η a
  k-law₁' = pr₁ (pr₂ (pr₂ (pr₂ 𝔸)))

  k-law₀' : (a : A) → is-defined (⟦ 𝕔 𝕜 · 𝕔 a ⟧)
  k-law₀' a = ·-is-defined-left 𝒜 (𝕔 𝕜 · 𝕔 a) (𝕔 𝕜)
   (≡-is-defined-left ⟦ 𝕔 𝕜 · 𝕔 a · 𝕔 𝕜  ⟧ (η a) (k-law₁' a 𝕜))

  s-law₁' : (a b : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b ⟧
  s-law₁' = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))

  s-law₀' : (a : A) → is-defined ⟦ 𝕔 𝕤 · 𝕔 a  ⟧
  s-law₀' a = ·-is-defined-left 𝒜 (𝕔 𝕤 · 𝕔 a) (𝕔 𝕜) (s-law₁' a 𝕜)

  s-law₂' : (a b c : A)
          → ⟦ 𝕔 a · 𝕔 c · (𝕔 b · 𝕔 c) ⟧ ≼ ⟦ 𝕔 𝕤 · 𝕔 a · 𝕔 b · 𝕔 c  ⟧
  s-law₂' = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ 𝔸))))
