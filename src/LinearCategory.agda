module LinearCategory where

open import MLTT.Spartan hiding (_+_)
open import UF.Sets

open import CommRing
open import Algebra

record category-structure (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    ob : (𝓤 ̇ )
    hom : ob → ob → (𝓥 ̇ )
    idn : (A : ob) → hom A A
    _⨾_ : {A B C : ob} → (f : hom A B) → (g : hom B C) → hom A C
  
  infixl 30 _⨾_

record precategory-axioms (str : category-structure 𝓤 𝓥) : 𝓤 ⊔ 𝓥 ̇ where
  no-eta-equality
  open category-structure str
  field
    hom-is-set : (A B : ob) → is-set (hom A B)
    idn-L : ∀ {A B} → (f : hom A B) → idn A ⨾ f ＝ f
    idn-R : ∀ {A B} → (f : hom A B) → f ⨾ idn B ＝ f
    assoc : ∀ {A B C D} {f : hom A B} {g : hom B C} {h : hom C D} → f ⨾ (g ⨾ h) ＝ (f ⨾ g) ⨾ h

record hom-is-algebra (R : CommRing 𝓥) (str : category-structure 𝓤 𝓥) : 𝓤 ⊔ 𝓥 ̇ where
  no-eta-equality
  open category-structure str
  field
    is-k-linear : (A B : ob) → algebra-on R (hom A B)

record linear-precategory (𝓤 𝓥 : Universe) (R : CommRing 𝓥) : (𝓤 ⊔ 𝓥) ⁺  ̇ where
  field
    str : category-structure 𝓤 𝓥
    is-precategory : precategory-axioms str
    is-k-linear : hom-is-algebra R str

  open category-structure str public
  open precategory-axioms is-precategory public
  open hom-is-algebra is-k-linear public
