open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_ ; _++_)
open import Cat.Base
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso)
open import Data.List
open import Data.List.Properties

module Multicategory.Representable where

-- The representable multicategory of a monoidal category.
--
-- A multimorphism Γ ⟶ τ is a unary morphism (⊗ Γ) ⟶ τ in C, where ⊗ Γ
-- right-associates the tensor product over the (list) context and the empty
-- context is the tensor unit.  Because contexts are lists, ⊗-context is a plain
-- fold that reduces through _++_ definitionally — so the rebracketing isos used
-- in composition are reducing, and the law boundaries (plain list ≡s) are seen
-- through by ⊗-context.  This is what makes the laws tractable here, where they
-- were blocked in the Vec-based version.
representable-multicategory
  : ∀ {o h} (C : Precategory o h) → Monoidal-category C → Premulticategory o h
representable-multicategory C M = Mc where
  open Cr C
  open Monoidal-category M
  open Premulticategory

  ⊗-context : List Ob → Ob
  ⊗-context []       = Unit
  ⊗-context (x ∷ Γ)  = x ⊗ ⊗-context Γ

  -- Tensor of a concatenation splits into the tensors of the parts; reducing.
  ⊗-context-++ : (Γ Δ : List Ob)
    → ⊗-context (Γ ++ Δ) ≅ (⊗-context Γ ⊗ ⊗-context Δ)
  ⊗-context-++ []      Δ = λ≅
  ⊗-context-++ (x ∷ Γ) Δ = ▶.F-map-iso (⊗-context-++ Γ Δ) ∙Iso (α≅ Iso⁻¹)

  -- Three-way split.
  ⊗-context-++-++ : (A B C : List Ob)
    → ⊗-context (A ++ B ++ C) ≅ (⊗-context A ⊗ (⊗-context B ⊗ ⊗-context C))
  ⊗-context-++-++ A B C =
    ⊗-context-++ A (B ++ C) ∙Iso ▶.F-map-iso (⊗-context-++ B C)

  -- Plug g into the slot x of f's domain: rebracket ⊗(Θ ++ Γ ++ Ξ) so that ⊗Γ
  -- sits where x was, apply g there (whiskered with identities), and rebracket
  -- back to ⊗(Θ ++ x ∷ Ξ).  Composition is then f ∘ plug.
  plug : ∀ {x} (Θ Γ Ξ : List Ob)
    → Hom (⊗-context Γ) x
    → Hom (⊗-context (Θ ++ Γ ++ Ξ)) (⊗-context (Θ ++ x ∷ Ξ))
  plug {x} Θ Γ Ξ g =
        (⊗-context-++ Θ (x ∷ Ξ)) .from
    ∘   (⊗-context Θ ▶ (g ◀ ⊗-context Ξ))
    ∘   (⊗-context-++-++ Θ Γ Ξ) .to

  Mc : Premulticategory _ _
  Mc .Obₘ = Ob

  Mc .Homₘ Γ τ = Hom (⊗-context Γ) τ

  Mc .Homₘ-set = Hom-set _ _

  Mc .idₘ {x} = ρ← x

  Mc ._∘ₘ_ {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {x = x} f g = f ∘ plug Θ Γ Ξ g

  -- Each law reduces, via the reducing ⊗-context-++ isos, to the corresponding
  -- monoidal coherence: the triangle for the unit laws, the pentagon for
  -- associativity, bifunctoriality for interchange.
  Mc .idₘl f        = {!!}
  Mc .idₘr f        = {!!}
  Mc .assocₘ f g h    = {!!}
  Mc .interchangeₘ f g h = {!!}
