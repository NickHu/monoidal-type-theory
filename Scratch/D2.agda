module Scratch.D2 where

-- D1 experiment: Comparison factors through Reindex.
--
--   Str --Reindex--> Unary Mᵣ --Unwrap--> C
--
-- `Unwrap` is the monoidal-specific equivalence Unary Mᵣ ≃ C (F₀ = identity on
-- objects, F₁ = precompose ρ→).  Comparison is *definitionally* Unwrap F∘
-- Reindex on F₀ and F₁ (only the F-id/F-∘ proofs differ, which Functor-path
-- absorbs), so Comparison-is-equivalence follows from Equivalence.agda's
-- general Reindex-is-equivalence + is-equivalence-∘.

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base using (Functor-path)
open import Cat.Functor.Properties
open import Cat.Functor.Equivalence
import Cat.Reasoning as Cr
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory
open import Multicategory.Unary
open import Multicategory.Instances.Monoidal
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Strictification.Equivalence as StrEq
import Multicategory.Instances.Monoidal.Coherence as Coh

module _ {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using (⊗-context ; plug)

  private
    Mᵣ : Premulticategory o h
    Mᵣ = monoidal→multicategory C M₀

    rep : Rep.is-representable Mᵣ
    rep = monoidal→multicategory-is-representable C M₀

  open Strict Mᵣ rep using (Str)
  open StrEq Mᵣ rep using (Reindex ; Reindex-is-equivalence)
  open Coh C M₀ using (Comparison ; plug-sing)

  -- The monoidal-specific half: Unary Mᵣ ≃ C by unwrapping the unit.
  Unwrap : Functor (Unary Mᵣ) C
  Unwrap .Functor.F₀ x   = x
  Unwrap .Functor.F₁ {x} m = m ∘ ρ→ x
  Unwrap .Functor.F-id   = ρ≅ .invr
  Unwrap .Functor.F-∘ {x} g f =
      ap (_∘ ρ→ x) (ap (g ∘_) (plug-sing x _ f))
    ∙ pullr (sym (assoc _ _ _))
    ∙ assoc _ _ _

  Unwrap-is-equivalence : is-equivalence Unwrap
  Unwrap-is-equivalence = ff+split-eso→is-equivalence
    (λ {x} {y} → invertible-precomp-equiv (iso→invertible (ρ≅ {x})))
    (λ y → y , id-iso)

  -- Comparison ≡ Unwrap F∘ Reindex: F₀ and F₁ agree definitionally.
  Comparison-factors : Comparison ≡ Unwrap F∘ Reindex
  Comparison-factors = Functor-path (λ Γ → refl) (λ f → refl)

  -- The equivalence, by composition — no ff/eso proof for Comparison needed.
  Comparison-is-equivalence' : is-equivalence Comparison
  Comparison-is-equivalence' = subst is-equivalence (sym Comparison-factors)
    (is-equivalence-∘ Unwrap-is-equivalence Reindex-is-equivalence)
