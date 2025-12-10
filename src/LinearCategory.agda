module LinearCategory where

open import MLTT.Spartan hiding (_+_)
open import UF.Sets

open import CommRing
open import Module

record category-structure (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    ob : 𝓤 ̇
    hom : ob → ob → 𝓥 ̇
    idn : (A : ob) → hom A A
    _⨾_ : {A B C : ob} → (f : hom A B) → (g : hom B C) → hom A C

  infixl 30 _⨾_

module addition-notation (R : CommRing 𝓥) (str : category-structure 𝓤 𝓥) where
  addition : (H : 𝓥 ̇ ) → module-on R H → H → H → H
  addition H M = module-on._+_ M

  syntax addition H is-mod x y = x +⟨ H , is-mod ⟩ y

  smul : (H : 𝓥 ̇ ) → module-on R H → ⟨ R ⟩ → H → H
  smul H M = module-on._·_ M

  syntax smul H is-mod x y = x ·⟨ H , is-mod ⟩ y

record linear-precategory-axioms (R : CommRing 𝓥) (str : category-structure 𝓤 𝓥) : 𝓤 ⊔ 𝓥 ̇ where
  no-eta-equality
  open category-structure str
  open addition-notation R str
  open comm-ring-on (R .pr₂) renaming (_*_ to _*ᴿ_; _+_ to _+ᴿ_)
  field
    homMod : (A B : ob) → module-on R (hom A B)
    idn-L : ∀ {A B} → (f : hom A B) → idn A ⨾ f ＝ f
    idn-R : ∀ {A B} → (f : hom A B) → f ⨾ idn B ＝ f
    assoc : ∀ {A B C D} (f : hom A B) (g : hom B C) (h : hom C D) → f ⨾ (g ⨾ h) ＝ (f ⨾ g) ⨾ h

    linearL : ∀ {A B C : ob} → (a b : hom A B) → (c : hom B C) →
      (a +⟨ hom A B , homMod A B ⟩ b) ⨾ c ＝ (a ⨾ c) +⟨ hom A C , homMod A C ⟩ (b ⨾ c)
    linearR : ∀ {A B C : ob} → (a : hom A B) → (b c : hom B C) →
      a ⨾ (b +⟨ hom B C , homMod B C ⟩ c) ＝ (a ⨾ b) +⟨ hom A C , homMod A C ⟩ (a ⨾ c)
    compatible : ∀ {A B C : ob} → (r s : ⟨ R ⟩) → (a : hom A B) (b : hom B C) →
      (r ·⟨ hom A B , homMod A B ⟩ a) ⨾ (s ·⟨ hom B C , homMod B C ⟩ b) ＝ (r *ᴿ s) ·⟨ hom A C , homMod A C ⟩ (a ⨾ b)

record linear-precategory (𝓤 𝓥 : Universe) (R : CommRing 𝓥) : (𝓤 ⊔ 𝓥) ⁺  ̇ where
  field
    str : category-structure 𝓤 𝓥
    ax : linear-precategory-axioms R str

  open category-structure str public
  open linear-precategory-axioms ax public
