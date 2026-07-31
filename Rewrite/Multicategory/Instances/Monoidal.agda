open import Rewrite.Multicategory

open import 1Lab.Prelude hiding (id; _∘_)
open import 1Lab.Reflection.Regularity using (module Regularity)
open import Cat.Base
open import Cat.Solver
open import Cat.Univalent
open import Cat.Monoidal.Base
import Cat.Monoidal.Reasoning
open import Data.List
open import ListPath.Boundary
open import ListPath.Tensor

module Rewrite.Multicategory.Instances.Monoidal where

unquoteDecl slot-unbury-chain = declare-chain slot-unbury-chain (quote slot-unbury)
  (● ⊛ ((● ⊛ (◆ ⊛ ●)) ⊛ ●)) ((● ⊛ ●) ⊛ (◆ ⊛ (● ⊛ ●)))

private variable
  o h : Level

monoidal→multicategory : (C : Precategory o h) → Monoidal-category C → Premulticategory o h
monoidal→multicategory C is-monoidal = M where
  open Cat.Monoidal.Reasoning is-monoidal
  open Tensor is-monoidal
  open Premulticategory

  ⊗-pull : ∀ {xs₁ x xs₂} → ⊗-context (xs₁ ++ x ∷ xs₂) ≅ ⊗-context xs₁ ⊗ x ⊗ ⊗-context xs₂
  ⊗-pull = tensor!

  ⊗-pull-list : ∀ {xs₁ ys xs₂} → ⊗-context (xs₁ ++ ys ++ xs₂) ≅ ⊗-context xs₁ ⊗ ⊗-context ys ⊗ ⊗-context xs₂
  ⊗-pull-list = tensor!

  plug : ∀ {ys₁ xs ys₂ : List Ob} {y}
    → Hom (⊗-context xs) y
    → Hom (⊗-context (ys₁ ++ xs ++ ys₂)) (⊗-context (ys₁ ++ y ∷ ys₂))
  plug {ys₁} {xs} {ys₂} g =
        (⊗-pull {ys₁} .from
          ∘ (⊗-context ys₁ ▶ (g ◀ ⊗-context ys₂)))
        ∘ (⊗-pull-list {ys₁} {xs} .to)

  ∷∘ₘ : ∀ {y ys₁ ys₂} {xs} (g : Hom (⊗-context xs) y) → plug {y ∷ ys₁} {xs} {ys₂} g ≡ y ▶ plug {ys₁} {xs} g
  ∷∘ₘ {y} {ys₁} {ys₂} {xs} g =
    plug {y ∷ ys₁} g
      ≡⟨⟩
    ((((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
       ∘ α→ (y , ⊗-context ys₁ , y ⊗ ⊗-context ys₂))
      ∘ ⌜ (y ⊗ ⊗-context ys₁) ▶ (y ▶ id) ⌝)
     ∘ ((y ⊗ ⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂)))
      ∘ ((y ⊗ ⊗-context ys₁)
         ▶ (⊗-context xs ▶ id) ∘ _≅_.to (⊗-context-++ xs ys₂))
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ ap! {! !} ⟩
    (⌜ ((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
        ∘ α→ (y , ⊗-context ys₁ , y ⊗ ⊗-context ys₂))
         ∘ id ⌝
     ∘ ((y ⊗ ⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂)))
      ∘ ((y ⊗ ⊗-context ys₁)
         ▶ (⊗-context xs ▶ id) ∘ _≅_.to (⊗-context-++ xs ys₂))
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ ap! {! !} ⟩
    (((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
      ∘ α→ (y , ⊗-context ys₁ , y ⊗ ⊗-context ys₂))
     ∘ ((y ⊗ ⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂)))
      ∘ ((y ⊗ ⊗-context ys₁)
         ▶ ⌜ (⊗-context xs ▶ id) ∘ _≅_.to (⊗-context-++ xs ys₂) ⌝)
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ ap! {! !} ⟩
    (((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
      ∘ α→ (y , ⊗-context ys₁ , y ⊗ ⊗-context ys₂))
     ∘ ((y ⊗ ⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂)))
      ∘ ((y ⊗ ⊗-context ys₁) ▶ _≅_.to (⊗-context-++ xs ys₂))
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ cat! C ⟩
    ((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
      ∘ ⌜ (α→ (y , ⊗-context ys₁ , y ⊗ ⊗-context ys₂)
     ∘ ((y ⊗ ⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂))) ⌝)
      ∘ (((y ⊗ ⊗-context ys₁) ▶ _≅_.to (⊗-context-++ xs ys₂))
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂)))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ ap! {! ▶-assoc !} ⟩
    ((y ▶ _≅_.from (⊗-context-++ ys₁ (y ∷ ys₂)))
      ∘ ((y ▶ ((⊗-context ys₁) ▶ (g ◀ ⊗-context ys₂))) ∘ α→ (y , ⊗-context ys₁ , ⊗-context xs ⊗ ⊗-context ys₂)))
      ∘ (((y ⊗ ⊗-context ys₁) ▶ _≅_.to (⊗-context-++ xs ys₂))
      ∘ α← (y , ⊗-context ys₁ , ⊗-context (xs ++ ys₂)))
      ∘ (y ▶ _≅_.to (⊗-context-++ ys₁ (xs ++ ys₂)))
      ≡⟨ {! !} ⟩
    y ▶ plug {ys₁} g
      ∎

  M : Premulticategory _ _
  M .Obₘ = Ob
  M .Homₘ xs = Hom (⊗-context xs)
  M .Homₘ-set {xs} {y} = Hom-set (⊗-context xs) y

  M .idₘ {x} = ρ← x
  _∘ₘ_ M {xs} {ys₁} {ys₂} {y} {z} f g =
    f ∘ plug {ys₁} g

  M .idₘl {x} {y} f =
    ρ← y
      ∘ ((λ← (y ⊗ Unit) ∘ ⌜ Unit ▶ (y ▶ id) ⌝) ∘ (Unit ▶ (f ◀ Unit)))
      ∘ (Unit ▶ ((x ⊗ Unit) ▶ id) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit))
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (-⊗-.▶.elim (-⊗-.▶.elim refl)) ⟩
    ρ← y
      ∘ (⌜ λ← (y ⊗ Unit) ∘ id ⌝ ∘ (Unit ▶ (f ◀ Unit)))
      ∘ (Unit ▶ ((x ⊗ Unit) ▶ id) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit))
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (elimr refl) ⟩
    ρ← y
      ∘ (λ← (y ⊗ Unit) ∘ (Unit ▶ (f ◀ Unit)))
      ∘ (Unit ▶ ⌜ (x ⊗ Unit) ▶ id ⌝ ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit))
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (-⊗-.▶.elim refl) ⟩
    ρ← y
      ∘ (λ← (y ⊗ Unit) ∘ (Unit ▶ (f ◀ Unit)))
      ∘ (Unit ▶ ⌜ id ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit) ⌝)
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (eliml refl) ⟩
    ρ← y
      ∘ ⌜ λ← (y ⊗ Unit) ∘ (Unit ▶ (f ◀ Unit)) ⌝
      ∘ (Unit ▶ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit))
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (_=>_.is-natural unitor-l.from _ _ _) ⟩
    ρ← y
      ∘ ((f ◀ Unit) ∘ λ← ((x ⊗ Unit) ⊗ Unit))
      ∘ ⌜ Unit ▶ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit) ⌝
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (-⊗-.▶.F-∘ _ _) ⟩
    ρ← y
      ∘ ⌜ ((f ◀ Unit) ∘ λ← ((x ⊗ Unit) ⊗ Unit))
            ∘ ((Unit ▶ α← (x , Unit , Unit)) ∘ (Unit ▶ (x ▶ λ→ Unit)))
            ∘ λ→ (x ⊗ Unit) ⌝
      ≡⟨ ap! (pulll refl) ⟩
    ρ← y
      ∘ ⌜ ((f ◀ Unit) ∘ λ← ((x ⊗ Unit) ⊗ Unit))
            ∘ (Unit ▶ α← (x , Unit , Unit))
            ∘ (Unit ▶ (x ▶ λ→ Unit)) ⌝
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (pull-inner refl) ⟩
    ρ← y
      ∘ ((f ◀ Unit)
         ∘ ⌜ λ← ((x ⊗ Unit) ⊗ Unit) ∘ (Unit ▶ α← (x , Unit , Unit)) ⌝
         ∘ (Unit ▶ (x ▶ λ→ Unit)))
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (_=>_.is-natural unitor-l.from _ _ _) ⟩
    ρ← y
      ∘ ((f ◀ Unit)
         ∘ ⌜ (α← (x , Unit , Unit) ∘ λ← (x ⊗ Unit ⊗ Unit))
               ∘ (Unit ▶ (x ▶ λ→ Unit)) ⌝)
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (pullr refl) ⟩
    ρ← y
      ∘ ((f ◀ Unit)
         ∘ α← (x , Unit , Unit)
         ∘ ⌜ λ← (x ⊗ Unit ⊗ Unit) ∘ (Unit ▶ (x ▶ λ→ Unit)) ⌝)
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (_=>_.is-natural unitor-l.from _ _ _) ⟩
    ρ← y
      ∘ ⌜ (f ◀ Unit) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit) ∘ λ← (x ⊗ Unit) ⌝
      ∘ λ→ (x ⊗ Unit)
      ≡⟨ ap! (pulll3 refl) ⟩
    ρ← y
      ∘ ⌜ (((f ◀ Unit) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit)) ∘ λ← (x ⊗ Unit))
            ∘ λ→ (x ⊗ Unit) ⌝
      ≡⟨ ap! (cancelr (λ≅ .invr)) ⟩
    ρ← y ∘ (f ◀ Unit) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit)
      ≡⟨ pulll refl ⟩
    ⌜ ρ← y ∘ (f ◀ Unit) ⌝ ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit)
      ≡⟨ ap! (_=>_.is-natural unitor-r.from _ _ _) ⟩
    (f ∘ ρ← (x ⊗ Unit)) ∘ α← (x , Unit , Unit) ∘ (x ▶ λ→ Unit)
      ≡⟨ pull-inner refl ⟩
    f ∘ (⌜ ρ← (x ⊗ Unit) ⌝ ∘ α← (x , Unit , Unit)) ∘ (x ▶ λ→ Unit)
      ≡⟨ ap! ρx⊗I≡ρx◀I ⟩
    f ∘ ⌜ (ρ← x ◀ Unit) ∘ α← (x , Unit , Unit) ⌝ ∘ (x ▶ λ→ Unit)
      ≡⟨ ap! triangle ⟩
    f ∘ ⌜ (x ▶ λ← Unit) ∘ (x ▶ λ→ Unit) ⌝
      ≡⟨ ap! (sym (-⊗-.▶.F-∘ _ _)) ⟩
    f ∘ (x ▶ ⌜ λ← Unit ∘ λ→ Unit ⌝)
      ≡⟨ ap! (λ≅ .invr) ⟩
    f ∘ ⌜ x ▶ id ⌝
      ≡⟨ ap! -⊗-.▶.F-id ⟩
    f ∘ id
      ≡⟨ elimr refl ⟩
    f
    ∎ where
      ρx⊗I≡ρx◀I : ρ← (x ⊗ Unit) ≡ ρ← x ◀ Unit
      ρx⊗I≡ρx◀I =
        ρ← (x ⊗ Unit)
          ≡⟨ insertl (ρ≅ .invl) ⟩
        ρ→ x ∘ ⌜ ρ← x ∘ ρ← (x ⊗ Unit) ⌝
          ≡⟨ ap! (sym (_=>_.is-natural unitor-r.from _ _ _)) ⟩
        ρ→ x ∘ ρ← x ∘ (ρ← x ◀ Unit)
          ≡⟨ cancell (ρ≅ .invl) ⟩
        ρ← x ◀ Unit
          ∎
  M .idₘr {xs₁} {xs₂} {x} f =
    f
      ∘ ((_≅_.from (⊗-context-++ xs₁ (x ∷ xs₂)) ∘ (⊗-context xs₁ ▶ (x ▶ id)))
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
      ∘ (⊗-context xs₁
         ▶ ((x ⊗ Unit) ▶ id)
           ∘ α← (x , Unit , ⊗-context xs₂)
           ∘ (x ▶ λ→ (⊗-context xs₂)))
      ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
      ≡⟨ ap (f ∘_) ⊗-context-++-triangle ⟩
    f ∘ id
      ≡⟨ elimr refl ⟩
    f
      ∎ where
      ⊗-context-++-triangle : _ ≡ id
      ⊗-context-++-triangle =
        ((_≅_.from (⊗-context-++ xs₁ (x ∷ xs₂)) ∘ (⊗-context xs₁ ▶ ⌜ x ▶ id ⌝))
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
          ∘ (⊗-context xs₁
             ▶ ((x ⊗ Unit) ▶ id)
               ∘ α← (x , Unit , ⊗-context xs₂)
               ∘ (x ▶ λ→ (⊗-context xs₂)))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (-⊗-.▶.elim refl) ⟩
        (⌜ _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂)) ∘ (⊗-context xs₁ ▶ id) ⌝
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
          ∘ (⊗-context xs₁
             ▶ ((x ⊗ Unit) ▶ id)
               ∘ α← (x , Unit , ⊗-context xs₂)
               ∘ (x ▶ λ→ (⊗-context xs₂)))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (-⊗-.▶.elimr refl) ⟩
        (_≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
          ∘ (⊗-context xs₁
             ▶ ⌜ (x ⊗ Unit) ▶ id ⌝
               ∘ α← (x , Unit , ⊗-context xs₂)
               ∘ (x ▶ λ→ (⊗-context xs₂)))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (-⊗-.▶.elim refl) ⟩
        (_≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
          ∘ (⊗-context xs₁
             ▶ ⌜ id
                   ∘ α← (x , Unit , ⊗-context xs₂)
                   ∘ (x ▶ λ→ (⊗-context xs₂)) ⌝)
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (eliml refl) ⟩
        (_≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
         ∘ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂)))
          ∘ (⊗-context xs₁
             ▶ α← (x , Unit , ⊗-context xs₂) ∘ (x ▶ λ→ (⊗-context xs₂)))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ pull-inner refl ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ ⌜ (⊗-context xs₁ ▶ (ρ← x ◀ ⊗-context xs₂))
                ∘ (⊗-context xs₁
                   ▶ α← (x , Unit , ⊗-context xs₂) ∘ (x ▶ λ→ (⊗-context xs₂))) ⌝
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (-⊗-.▶.packl refl) ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ (⊗-context xs₁
             ▶ ⌜ (ρ← x ◀ ⊗-context xs₂)
                   ∘ α← (x , Unit , ⊗-context xs₂)
                   ∘ (x ▶ λ→ (⊗-context xs₂)) ⌝)
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (pulll refl) ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ (⊗-context xs₁
             ▶ ⌜ (ρ← x ◀ ⊗-context xs₂) ∘ α← (x , Unit , ⊗-context xs₂) ⌝
               ∘ (x ▶ λ→ (⊗-context xs₂)))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! triangle ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ (⊗-context xs₁
             ▶ ⌜ (x ▶ λ← (⊗-context xs₂)) ∘ (x ▶ λ→ (⊗-context xs₂)) ⌝)
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ ap! (-⊗-.▶.annihilate (λ≅ .invr)) ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ ⌜ (⊗-context xs₁ ▶ id) ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂)) ⌝
          ≡⟨ ap! (-⊗-.▶.eliml refl) ⟩
        _≅_.from (⊗-context-++ xs₁ (x ∷ xs₂))
          ∘ _≅_.to (⊗-context-++ xs₁ (x ∷ xs₂))
          ≡⟨ _≅_.invr (⊗-context-++ xs₁ (x ∷ xs₂)) ⟩
        id
          ∎
  M .assocₘ {ws} {xs₁} {xs₂} {ys₁} {ys₂} {x} {y} {z} f g h = Hom-pathp-refll C (
    (_∘ₘ_ M {ws} {ys₁ ++ xs₁} {xs₂ ++ ys₂}
       ⌜ subst (λ xs → M .Homₘ xs z) (slot-unbury ys₁ xs₁ x xs₂ ys₂)
           ((_∘ₘ_ M {xs₁ ++ x ∷ xs₂} {ys₁} {ys₂} f) g) ⌝) h
      ∘ _≅_.from
          (path→iso (λ i → ⊗-context (assoc-boundary ys₁ xs₁ ws xs₂ ys₂ i)))
      ≡⟨ ap!
           (sym
              (from-pathp-from' C (ap ⊗-context (slot-unbury ys₁ xs₁ x xs₂ ys₂))
                 (transport-filler
                    (λ i → Hom (⊗-context (slot-unbury ys₁ xs₁ x xs₂ ys₂ i)) z)
                    ((_∘ₘ_ M {xs₁ ++ x ∷ xs₂} {ys₁} {ys₂} f) g)))) ⟩
    (_∘ₘ_ M {ws} {ys₁ ++ xs₁} {xs₂ ++ ys₂}
       ((_∘ₘ_ M {xs₁ ++ x ∷ xs₂} {ys₁} {ys₂} f g)
        ∘ _≅_.from (path→iso (ap ⊗-context (slot-unbury ys₁ xs₁ x xs₂ ys₂)))) h)
      ∘ _≅_.from
          (path→iso (λ i → ⊗-context (assoc-boundary ys₁ xs₁ ws xs₂ ys₂ i)))
      ≡⟨⟩
    (((f
       ∘ (⊗-pull {ys₁} {y} {ys₂} .from ∘ (⊗-context ys₁ ▶ (g ◀ ⊗-context ys₂)))
       ∘ ⊗-pull-list {ys₁} {xs₁ ++ x ∷ xs₂} {ys₂} .to)
      ∘ _≅_.from ⌜ path→iso (ap ⊗-context (slot-unbury ys₁ xs₁ x xs₂ ys₂)) ⌝)
     ∘ (⊗-pull {ys₁ ++ xs₁} {x} {xs₂ ++ ys₂} .from
        ∘ (⊗-context (ys₁ ++ xs₁) ▶ (h ◀ ⊗-context (xs₂ ++ ys₂))))
     ∘ ⊗-pull-list {ys₁ ++ xs₁} {ws} {xs₂ ++ ys₂} .to)
      ∘ _≅_.from
          (path→iso (λ i → ⊗-context (assoc-boundary ys₁ xs₁ ws xs₂ ys₂ i)))
      ≡⟨ ap! (slot-unbury-chain is-monoidal ys₁ xs₁ x xs₂ ys₂ .⊗-chain.char) ⟩
--   ⊗-context (ys₁ ++ xs₁) ⊗ x ⊗ ⊗-context (xs₂ ++ ys₂)
-- → ⊗-context ((ys₁ ++ xs₁) ++ x ∷ (xs₂ ++ ys₂))
-- → ⊗-context (ys₁ ++ (xs₁ ++ x ∷ xs₂) ++ ys₂)
-- → ⊗-context ys₁ ⊗ ⊗-context (xs₁ ++ x ∷ xs₂) ⊗ ⊗-context ys₂
    (((f
       ∘ (⊗-pull {ys₁} {y} {ys₂} .from ∘ (⊗-context ys₁ ▶ (g ◀ ⊗-context ys₂)))
       ∘ ⊗-pull-list {ys₁} {xs₁ ++ x ∷ xs₂} {ys₂} .to)
      ∘ _≅_.from
          (Tensor.⊗-chain.⊗iso
             (slot-unbury-chain is-monoidal ys₁ xs₁ x xs₂ ys₂)))
     ∘ (⊗-pull {ys₁ ++ xs₁} {x} {xs₂ ++ ys₂} .from
        ∘ (⊗-context (ys₁ ++ xs₁) ▶ (h ◀ ⊗-context (xs₂ ++ ys₂))))
     ∘ ⊗-pull-list {ys₁ ++ xs₁} {ws} {xs₂ ++ ys₂} .to)
      ∘ _≅_.from
          (path→iso (λ i → ⊗-context (assoc-boundary ys₁ xs₁ ws xs₂ ys₂ i)))
      -- ≡⟨ {! _≅_.from (Tensor.⊗-chain.⊗iso (slot-unbury-chain is-monoidal ys₁ xs₁ x xs₂ ys₂)) !} ⟩
      ≡⟨ {! path→iso (ap ⊗-context (slot-unbury ys₁ xs₁ x xs₂ ys₂)) !} ⟩
    {! !}
      ≡⟨ {! !} ⟩
    (_∘ₘ_ M {xs₁ ++ ws ++ xs₂} {ys₁} {ys₂} f) ((_∘ₘ_ M {ws} {xs₁} {xs₂} g) h)
      ∎
    )
  M .interchangeₘ f g h = {! !}

