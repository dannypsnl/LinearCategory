module Algebra where

open import MLTT.Spartan hiding (_+_)

open import CommRing
open import Module

record algebra-axioms {R : CommRing 𝓤} {V : 𝓤 ̇ } (str : module-on R V) (_*_ : V → V → V) : 𝓤 ̇ where
  no-eta-equality
  open comm-ring-on (R .pr₂) renaming (_*_ to _*ᴿ_; _+_ to _+ᴿ_; -_ to -ᴿ_)
  open module-on str
  field
    1a : V
    *-neuL : {v : V} → 1a * v ＝ v
    *-neuR : {v : V} → v * 1a ＝ v
    *-assoc : ∀ {a b c} → a * (b * c) ＝ (a * b) * c
    linearL : ∀ {a b c} → (a + b) * c ＝ (a * c) + (b * c)
    linearR : ∀ {a b c} → a * (b + c) ＝ (a * b) + (a * c)
    compatible : ∀ {r s a b} → (r · a) * (s · b) ＝ (r *ᴿ s) · (a * b)

record algebra-on (R : CommRing 𝓤) (V : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    module-str : module-on R V
    _*_ : V → V → V
    is-algebra : algebra-axioms module-str _*_

Algebra : (𝓤 : Universe) → (R : CommRing 𝓤) → 𝓤 ⁺  ̇
Algebra 𝓤 R = Σ X ꞉ 𝓤 ̇ , algebra-on R X
