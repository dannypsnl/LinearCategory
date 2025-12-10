module Module where

open import MLTT.Spartan hiding (_+_)
open import UF.Sets

open import CommRing

record module-axioms (R : CommRing 𝓤) {V : 𝓤 ̇ }
  (0v : V) (_+_ : V → V → V) (_·_ : ⟨ R ⟩ → V → V) (- : V → V)
  : 𝓤 ̇ where
  no-eta-equality
  open comm-ring-on (R .pr₂) renaming (_+_ to _+ᴿ_; -_ to -ᴿ_)
  field
    carrier-is-set : is-set V
    +-assoc : {u v w : V} → u + (v + w) ＝ (u + v) + w
    +-comm : {u v : V} → u + v ＝ v + u
    +-neu : {v : V} → 0v + v ＝ v
    +-cancel : {v : V} → v + - v ＝ 0v
    compatible : {a b : ⟨ R ⟩} {v : V} → a · (b · v) ＝ (a * b) · v
    scalar-neu : {v : V} → 1r · v ＝ v
    distribⱽ : {s : ⟨ R ⟩} {v w : V} → s · (v + w) ＝ (s · v) + (s · w)
    distribᴿ : {s t : ⟨ R ⟩} {v : V} → (s +ᴿ t) · v ＝ (s · v) + (t · v)

record module-on (R : CommRing 𝓤) (V : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    0v : V
    _+_ : V → V → V
    _·_ : ⟨ R ⟩ → V → V
    -_ : V → V
    is-module : module-axioms R 0v _+_ _·_ -_

  infixl 20 _+_
  infixl 30 _·_
  infix 40 -_

Module : (𝓤 : Universe) → (R : CommRing 𝓤) → 𝓤 ⁺  ̇
Module 𝓤 R = Σ X ꞉ 𝓤 ̇ , module-on R X
