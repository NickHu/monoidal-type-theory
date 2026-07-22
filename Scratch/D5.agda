module Scratch.D5 where

-- D3/D5 micro-experiments on nat-gen's hand-rolled bifunctor algebra:
--  * step-a (5 lines)                       = -⊗-.rlmap _ _   (1 line)
--  * ρ-whisker-collapse-to-φ (8 lines + 5)  = pulll rlmap ∙ cancelr (▶.annihilate ..)
--  * φ≡μ (8 lines)                          = 2 lines via cancelr (▶.annihilate ..)
--  * ρ-reindex-style swizzles (9-10 lines)  = 3 lines (intror/pulll/cancell)
--    [validated inside Scratch.D3's core already; here: the ρ←-reindex variant]

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base
import Cat.Reasoning as Cr
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory
open import Multicategory.Instances.Monoidal
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Instances.Monoidal.Coherence as Coh

module _ {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using
    (⊗-context ; φ ; ⊗-context-++ ; ⊗-context-++-idr ; ⊗-context-++-[]-ρ)
  open Coh C M₀ using (Fₘ ; μ-φ)

  private
    Mᵣ = monoidal→multicategory C M₀
    rep = monoidal→multicategory-is-representable C M₀
  open Strict Mᵣ rep using (μ)

  module _ {Γ Γ' Δ Δ' : List Ob}
    (f : Hom (⊗-context Γ ⊗ Unit) (⊗-context Γ'))
    (g : Hom (⊗-context Δ ⊗ Unit) (⊗-context Δ')) where

    private
      A  = ⊗-context Γ ; A' = ⊗-context Γ'
      B  = ⊗-context Δ ; B' = ⊗-context Δ'
      Ff = Fₘ Γ Γ' f
      Fg = Fₘ Δ Δ' g

    -- step-a is the bifunctor interchange, verbatim.
    step-a' : (A' ▶ ρ← B') ∘ (Ff ◀ (B' ⊗ Unit)) ≡ Ff ⊗₁ ρ← B'
    step-a' = -⊗-.rlmap _ _

    -- and the whole ρ-whisker collapse is interchange + a ▶-cancellation.
    ρ-whisker-collapse' :
      (A' ▶ ρ← B') ∘ ((Ff ◀ (B' ⊗ Unit)) ∘ (A ▶ ρ→ B')) ≡ Ff ◀ B'
    ρ-whisker-collapse' =
      pulll (-⊗-.rlmap _ _) ∙ cancelr (▶.annihilate (ρ≅ .invr))

  -- φ≡μ in two lines.
  φ≡μ' : (Γ Δ : List Ob) → φ Γ Δ ≡ μ Γ Δ ∘ (⊗-context Γ ▶ ρ→ (⊗-context Δ))
  φ≡μ' Γ Δ = sym
    (ap (_∘ (⊗-context Γ ▶ ρ→ (⊗-context Δ))) (μ-φ Γ Δ)
      ∙ cancelr (▶.annihilate (ρ≅ .invr)))

  -- ρ←-reindex via swizzle combinators (was ~19 lines with the where-block).
  ρ←-reindex' : (A : List Ob)
    → (⊗-context-++-idr A) .to ∘ (⊗-context-++ A []) .from ≡ ρ← (⊗-context A)
  ρ←-reindex' A =
      introl (ρ≅ .invr)
    ∙ pullr ( ap (_∘ ((⊗-context-++-idr A) .to ∘ (⊗-context-++ A []) .from))
                 (sym (⊗-context-++-[]-ρ A))
            ∙ cancel-inner (⊗-context-++-idr A .invr)
            ∙ ⊗-context-++ A [] .invl )
    ∙ idr _
