open import 1Lab.Prelude
open import Cat.Base
open import Cat.Univalent using (is-category)
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory

module Multicategory.Unary where

-- The underlying (unary) category of a multicategory: objects are the
-- multicategory's objects, and morphisms x → y are unary multimorphisms
-- Homₘ (x ∷ []) y.  Composition is _∘ₘ_ with empty prefix/suffix, and the
-- category laws are the multicategory laws specialised to singleton contexts,
-- where the list-path transports (slot-unbury, ++-idr, assocₘ-boundary) all
-- degenerate to refl.
module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M

  Unary : Precategory o h
  Unary .Precategory.Ob          = Obₘ
  Unary .Precategory.Hom x y     = Homₘ (x ∷ []) y
  Unary .Precategory.Hom-set _ _ = Homₘ-set
  Unary .Precategory.id          = idₘ
  Unary .Precategory._∘_ {x} g f = _∘ₘ_ {Θ = []} {Ξ = []} {Γ = x ∷ []} g f
  Unary .Precategory.idr f       = idₘl f
  Unary .Precategory.idl f       = idₘr {Γ = _ ∷ []} f
  -- assocₘ at singleton contexts: the boundary/slot-unbury list-paths are refl,
  -- but its `subst` over slot-unbury only reduces up to transport-refl.
  Unary .Precategory.assoc {w} f g h =
    sym (assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} f g h)
      ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} {Γ = w ∷ []} q h) (transport-refl (f ∘ₘ g))

  -- A multicategory is univalent when its underlying category is.
  is-multicategory : Type (o ⊔ h)
  is-multicategory = is-category Unary
