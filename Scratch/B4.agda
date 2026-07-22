module Scratch.B4 where

-- B4: F-α→-to (the .to-mirror of the monoidal-functor hexagon, currently 32
-- lines of manual factor-inversion via QS/MID/hexagon-to, lines 443-481)
-- is a 4-line corollary of F-α→ using Cat.Reasoning.swizzle +
-- ◀.cancel-inner/▶.cancell.  No new induction, no iso-packaging.

open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Data.List
open import Data.List.Properties
import Multicategory.Instances.Monoidal as MIM

module _ {o h} (C : Precategory o h) (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M
  open MIM.Repr C M using (⊗-context ; ⊗-context-++ ; ++-assoc-⊗-iso ; F-α→)

  module _ (Γ Δ Ξ : List Ob) where
    private
      A≅ = ++-assoc-⊗-iso Γ Δ Ξ
      P₁ = ⊗-context-++ Γ Δ
      P₂ = ⊗-context-++ (Γ ++ Δ) Ξ
      P₃ = ⊗-context-++ Γ (Δ ++ Ξ)
      P₄ = ⊗-context-++ Δ Ξ

    F-α→-to' :   (⊗-context Γ ▶ P₄ .to) ∘ P₃ .to ∘ A≅ .to
             ≡   α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
               ∘ (P₁ .to ◀ ⊗-context Ξ) ∘ P₂ .to
    F-α→-to' =
        ap ((⊗-context Γ ▶ P₄ .to) ∘_)
           ( swizzle (F-α→ Γ Δ Ξ) (◀.cancel-inner (P₁ .invr) ∙ P₂ .invr) (P₃ .invl)
           ∙ sym (assoc _ _ _) )
      ∙ ▶.cancell (P₄ .invl)
