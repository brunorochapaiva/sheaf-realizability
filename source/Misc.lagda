\begin{code}

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.Vector

module Misc where

 vmap-!! : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ}
           (f : X → Y)
           (xs : Vector X n)
           (p : Fin n)
         → f (xs !! p) ＝ vmap f xs !! p
 vmap-!! f (x ∷ xs) 𝟎       = refl
 vmap-!! f (x ∷ xs) (suc p) = vmap-!! f xs p


\end{code}
