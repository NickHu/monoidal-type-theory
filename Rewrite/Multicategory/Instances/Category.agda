open import Rewrite.Multicategory

open import 1Lab.Prelude hiding (id; _∘_)
open import 1Lab.Reflection.Regularity
open import Cat.Base
open import Data.List

module Rewrite.Multicategory.Instances.Category where

private variable
  o h : Level

category→multicategory : Precategory o h → Premulticategory o h
category→multicategory C = M where
  open Precategory C
  open Premulticategory

  M : Premulticategory _ _
  M .Obₘ = Ob
  M .Homₘ = homₘ where
    homₘ : List Ob → Ob → Type _
    homₘ []           y = Lift _ ⊥
    homₘ (x ∷ [])     y = Hom x y
    homₘ (x ∷ _ ∷ _)  y = Lift _ ⊥
  M .Homₘ-set {x ∷ []} = Hom-set _ _
  M .idₘ = id
  M ._∘ₘ_ {x ∷ []} {[]} {[]} {y} {z} f g = f ∘ g
  _∘ₘ_ M {x₂ ∷ []} {x₃ ∷ []} {[]} f g = absurd (lower f)
  M .idₘl = idl
  M .idₘr {[]} {[]} = idr
  M .idₘr {x ∷ []} {[]} f = absurd (lower f)
  M .assocₘ {x ∷ []} {xs₁ = []} {[]} {ys₁ = []} {[]} f g h = Regularity.precise! (sym (assoc f g h))
  M .assocₘ {xs₁ = x ∷ []} {ys₁ = []} {[]} f g h = absurd (lower g)
  M .assocₘ {ys₁ = x ∷ []} f g h = absurd (lower f)
  M .interchangeₘ {xs₁ = []} {[]} f g h = absurd (lower f)
  M .interchangeₘ {xs₁ = x ∷ []} f g h = absurd (lower f)
