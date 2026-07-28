-- Client-side regression test for tensor!: record/module opens at use
-- sites mint fresh definitionally-equal copies of _⊗_ and ⊗-context,
-- so the macro must match up to conversion, not by name.  This file
-- exercises tensor! from OUTSIDE ListPath.Tensor.
module ListPath.TensorClient where
open import 1Lab.Prelude hiding (id; _∘_)
open import Cat.Base
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Data.List
open import ListPath.Tensor

module _ {o h} {C : Precategory o h} (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M
  open Tensor M

  _ : (ys₁ : List Ob) (y : Ob) (ys₂ : List Ob)
    → ⊗-context (ys₁ ++ y ∷ ys₂) ≅ (⊗-context ys₁ ⊗ (y ⊗ ⊗-context ys₂))
  _ = λ ys₁ y ys₂ → tensor!
