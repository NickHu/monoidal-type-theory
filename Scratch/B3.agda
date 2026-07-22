module Scratch.B3 where

-- B3: 1lab reasoning-combinator rewrites.
--  (a) idₘl's mid≡id + plug-ρ (lines 515-544, 26 lines) → 4 lines via
--      ▶.annihilate + cancell.
--  (b) idₘr's intro-eq (563-577, 15 lines) → 3 lines via ▶.pulll;
--      unit-cancel (581-595, 15 lines) → 1 line via ▶.cancell;
--      plug-unit-core (604-638, 35 lines) → 9 lines via pulll/cancelr/▶.pulll/
--      ▶.pushl.
--  (c) the to-pathp + transport-⊗-red discharge of idₘr (546, 640-647) is
--      subsumed by Cat.Univalent.Hom-pathp-refll: no transport reasoning at
--      all, just the iso characterisation + the core equation.

open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso ; Hom-pathp-refll)
open import Cat.Functor.Naturality
open import Data.List
open import Data.List.Properties
import Cat.Bi.Reasoning
import Multicategory.Instances.Monoidal as MIM

module _ {o h} (C : Precategory o h) (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M
  open Cat.Bi.Reasoning (Deloop M) using (λ→nat ; λ←nat ; ρ←nat)
  open MIM.Repr C M using
    ( ⊗-context ; ⊗-context-++ ; ⊗-context-++-++ ; ⊗-context-++-idr
    ; ⊗-context-++-idr-path ; ⊗-context-++-[]-ρ ; plug )

  ----------------------------------------------------------------------
  -- (a) idₘl's plug-ρ: 26 lines → 4.
  ----------------------------------------------------------------------
  module _ (Θ Ξ : List Ob) (x : Ob) where
    private
      split = ⊗-context-++ Θ (x ∷ Ξ)
      ψ     = ⊗-context-++ (x ∷ []) Ξ

    plug-ρ' : plug Θ (x ∷ []) Ξ (ρ← x) ≡ id
    plug-ρ' =
        ap (split .from ∘_)
           (cancell (▶.annihilate (ap (_∘ ψ .to) (sym triangle-α→) ∙ ψ .invr)))
      ∙ split .invr

  ----------------------------------------------------------------------
  -- (b) idₘr's chain: 65 lines → ~13.
  ----------------------------------------------------------------------
  module _ (Γ : List Ob) {z : Ob} (f : Hom (⊗-context Γ) z) where
    private
      ρ-idr = ⊗-context-++-idr Γ
      intro : Hom (⊗-context Γ) (Unit ⊗ (⊗-context Γ ⊗ Unit))
      intro = (⊗-context-++-++ [] Γ []) .to ∘ ρ-idr .from

    intro-eq' : intro ≡ (Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
    intro-eq' =
        sym (assoc _ _ _)
      ∙ ap ((Unit ▶ (⊗-context-++ Γ []) .to) ∘_) (λ→nat (ρ-idr .from))
      ∙ ▶.pulll (⊗-context-++-[]-ρ Γ)

    unit-cancel' : (Unit ▶ ρ← (⊗-context Γ)) ∘ intro ≡ λ→ (⊗-context Γ)
    unit-cancel' =
      ap ((Unit ▶ ρ← (⊗-context Γ)) ∘_) intro-eq' ∙ ▶.cancell (ρ≅ .invr)

    plug-unit-core' : (ρ← z ∘ plug [] Γ [] f) ∘ ρ-idr .from ≡ f
    plug-unit-core' =
        sym (assoc _ _ _)
      ∙ ap (ρ← z ∘_)
           (sym (assoc _ _ _) ∙ ap (λ← (z ⊗ Unit) ∘_) (sym (assoc _ _ _)))
      ∙ pulll (sym (λ←nat (ρ← z)))
      ∙ sym (assoc _ _ _)
      ∙ ap (λ← z ∘_)
          ( ▶.pulll (ρ←nat f)
          ∙ ▶.pushl refl
          ∙ ap ((Unit ▶ f) ∘_) unit-cancel' )
      ∙ pulll (λ←nat f)
      ∙ cancelr (λ≅ .invr)

    ----------------------------------------------------------------------
    -- (c) the law itself via Hom-pathp-refll: no to-pathp/transport steps.
    ----------------------------------------------------------------------
    idₘr' : PathP (λ i → Hom (⊗-context (++-idr Γ i)) z)
              (ρ← z ∘ plug [] Γ [] f) f
    idₘr' = Hom-pathp-refll C
      ( ap ((ρ← z ∘ plug [] Γ [] f) ∘_)
           (ap (λ i → i .from) (⊗-context-++-idr-path Γ))
      ∙ plug-unit-core' )
