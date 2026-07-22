module Scratch.B1refute where

-- B1(i) refutation: the hypothesis "each list-reassoc helper path equals
-- ap (Θ ++_) (its [] base)" is ILL-TYPED for slot-unbury (and likewise
-- ic-slot₀/₁, assocₘ-flatten): the helper's codomain is (Θ ++ Φ) ++ y ∷ (Ψ ++ Ξ)
-- but ap (Θ ++_) of the base has codomain Θ ++ (Φ ++ y ∷ (Ψ ++ Ξ)), and these
-- are distinct neutral terms for variable Θ.  Expected: type error below.

open import 1Lab.Prelude
open import Data.List
open import Data.List.Properties
open import Multicategory

module _ {ℓ} {A : Type ℓ} (Θ Φ : List A) (y : A) (Ψ Ξ : List A) where
  bad : slot-unbury Θ Φ y Ψ Ξ ≡ ap (Θ ++_) (++-assoc Φ (y ∷ Ψ) Ξ)
  bad = refl
