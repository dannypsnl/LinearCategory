module alg-0000 where

open import MLTT.Spartan hiding (_+_)

open import CommRing
open import Algebra

module _ (K : CommRing 𝓤) (A : Algebra 𝓤 K) where
  open algebra-on (A .pr₂)
  open algebra-axioms (algebra-on.is-algebra (A .pr₂))

  -- Every algebra has at least an idempotent
  main : Σ e ꞉ ⟨ A ⟩ , e * e ＝ e
  main = 1a , *-neuL
