module CommRing where

open import MLTT.Spartan hiding (_+_)
open import UF.Sets

⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
⟨ X , s ⟩ = X

record comm-ring-axioms {X : 𝓤 ̇ } (0r 1r : X) (_+_ : X → X → X) (_*_ : X → X → X) (- : X → X) : 𝓤 ̇ where
  no-eta-equality
  field
    carrier-is-set : is-set X
    +-assoc : associative _+_
    +-idL : left-neutral 0r _+_
    +-idR : right-neutral 0r _+_
    +-cancel : ∀ {x} → x + - x ＝ 0r
    +-comm : ∀ {a b} → a + b ＝ b + a

    *-assoc : associative _*_
    *-idL : left-neutral 1r _*_
    *-idR : right-neutral 1r _*_
    *-comm : ∀ {a b} → a * b ＝ b * a

    distribL : ∀ {a b c} → (a + b) * c ＝ (a * c) + (b * c)
    distribR : ∀ {a b c} → c * (a + b) ＝ (c * a) + (c * b)

record comm-ring-on (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    0r 1r : X
    _+_ : X → X → X
    _*_ : X → X → X
    -_ : X → X
    is-comm-ring : comm-ring-axioms 0r 1r _+_ _*_ -_

  infixl 20 _+_
  infixl 30 _*_
  infix 40 -_

CommRing : (𝓤 : Universe) → 𝓤 ⁺  ̇
CommRing 𝓤 = Σ X ꞉ 𝓤 ̇ , comm-ring-on X
