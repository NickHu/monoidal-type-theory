open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory

module Multicategory.Functor where

-- Multifunctors between premulticategories.  A functor acts on contexts by
-- `map F₀`; since map does not commute with ++ definitionally, the
-- composition law is a PathP over the structural path map-++₂ below, with
-- the slot of the postcomposed arrow exposed by a subst along map-++ (the
-- same discipline as the laws in Multicategory.agda).

private variable
  o h o' h' : Level

-- map f (Θ ++ Γ ++ Ξ) ≡ map f Θ ++ map f Γ ++ map f Ξ, cons-by-cons.
map-++₂ : {A : Type o} {B : Type o'} (f : A → B) (Θ Γ Ξ : List A)
        → map f (Θ ++ Γ ++ Ξ) ≡ map f Θ ++ map f Γ ++ map f Ξ
map-++₂ f []      Γ Ξ = map-++ f Γ Ξ
map-++₂ f (a ∷ Θ) Γ Ξ = ap (f a ∷_) (map-++₂ f Θ Γ Ξ)

record Multifunctor (M : Premulticategory o h) (N : Premulticategory o' h')
       : Type (o ⊔ h ⊔ o' ⊔ h') where
  no-eta-equality
  private
    module M = Premulticategory M
    module N = Premulticategory N
  field
    F₀ : M.Obₘ → N.Obₘ
    F₁ : ∀ {Γ z} → M.Homₘ Γ z → N.Homₘ (map F₀ Γ) (F₀ z)

    -- map F₀ (x ∷ []) is definitionally F₀ x ∷ [], so this is homogeneous.
    F-idₘ : ∀ {x} → F₁ (M.idₘ {x}) ≡ N.idₘ

    F-∘ₘ : ∀ {Θ Ξ Γ x z} (f : M.Homₘ (Θ ++ x ∷ Ξ) z) (g : M.Homₘ Γ x)
         → PathP (λ i → N.Homₘ (map-++₂ F₀ Θ Γ Ξ i) (F₀ z))
             (F₁ (M._∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g))
             (N._∘ₘ_ {Θ = map F₀ Θ} {Ξ = map F₀ Ξ}
               (subst (λ Ω → N.Homₘ Ω (F₀ z)) (map-++ F₀ Θ (x ∷ Ξ)) (F₁ f))
               (F₁ g))
