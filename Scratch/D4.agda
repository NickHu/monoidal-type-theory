module Scratch.D4 where

-- D4 experiment: single packaged statement of the coherence theorem.
-- 1lab has no "monoidal equivalence" bundle (checked: Cat.Monoidal.Functor has
-- only Lax/Monoidal-functor-on + is-monoidal-transformation), so the cleanest
-- packaging is a Σ-type.  The strictness component is left as a parameter
-- (another reviewer designs the predicate); this validates that everything
-- else assembles into one theorem-shaped statement today.

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Equivalence
import Cat.Monoidal.Functor as MonF

open import Multicategory
open import Multicategory.Instances.Monoidal
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Instances.Monoidal.Coherence as Coh

module _ {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  private
    Mᵣ = monoidal→multicategory C M₀
    rep = monoidal→multicategory-is-representable C M₀

  open Strict Mᵣ rep using (Str ; Str-monoidal)
  open Coh C M₀ using (Comparison ; Comparison-monoidal ; Comparison-is-equivalence)

  -- "Every monoidal category admits a strong monoidal equivalence from a
  -- strict monoidal category."  Modulo the is-strict component, this is
  -- assembled purely from what Coherence.agda already proves.
  Monoidal-strictification
    : (is-strict : ∀ {o' h'} {S : Precategory o' h'} → Monoidal-category S → Type)
    → is-strict Str-monoidal
    → Σ[ S ∈ Precategory o h ]
      Σ[ Mₛ ∈ Monoidal-category S ]
      ( is-strict Mₛ
      × Σ[ F ∈ Functor S C ]
        ( MonF.Monoidal-functor-on Mₛ M₀ F
        × is-equivalence F ) )
  Monoidal-strictification is-strict str =
    Str , Str-monoidal , str , Comparison , Comparison-monoidal , Comparison-is-equivalence
