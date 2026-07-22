open import 1Lab.Prelude
open import Cat.Base
open import Cat.Functor.Properties
open import Cat.Functor.Equivalence
import Cat.Reasoning as Cr
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory
open import Multicategory.Unary
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict

-- The underlying category of the strictification `Str` is (weakly) equivalent to
-- the unary category `Unary M` of the original multicategory.  Since `Str` is
-- literally `Unary M` reindexed along the tensor `⊗₀ : List Obₘ → Obₘ`, the
-- comparison functor `Reindex : Str → Unary M` is the identity on hom-sets
-- (hence fully faithful) and split essentially surjective (every object y is the
-- tensor of the singleton context [y], via the universal arrow ⊗-arr [y]).
--
-- This module underlies the coherence theorem: in
-- Multicategory.Instances.Monoidal.Coherence, the comparison functor of
-- `monoidal-strictification` is defined as `Unwrap F∘ Reindex`, and its
-- equivalence proof composes `Reindex-is-equivalence` with the (monoidal-
-- specific) equivalence `Unary Mᵣ ≃ C`.
module Multicategory.Strictification.Equivalence
  {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where

  open Premulticategory M
  open Strict M rep using (Str ; ⊗₀ ; ⊗-arr ; ⊗-arr-univ)
  private module UR = Cr (Unary M)

  -- The comparison functor: reindex `Unary M` along `⊗₀`.  On hom-sets it is the
  -- identity (Str.Hom Γ Δ = Unary.Hom (⊗₀ Γ) (⊗₀ Δ) definitionally).
  Reindex : Functor Str (Unary M)
  Reindex .Functor.F₀      = ⊗₀
  Reindex .Functor.F₁ f    = f
  Reindex .Functor.F-id    = refl
  Reindex .Functor.F-∘ f g = refl

  -- Fully faithful: the action on hom-sets is the identity map.
  Reindex-ff : is-fully-faithful Reindex
  Reindex-ff = id-equiv

  -- The universal arrow of a singleton context exhibits ⊗₀ [y] ≅ y in Unary M.
  -- Precomposition with η = ⊗-arr [y] is an equivalence on hom-sets (universality
  -- at Θ = Ξ = []), so η is invertible; its inverse ε is the equivalence's
  -- preimage of the identity.
  sing-iso : (y : Obₘ) → UR._≅_ (⊗₀ (y ∷ [])) y
  sing-iso y = UR.make-iso ε η invl invr
    where
      η : UR.Hom y (⊗₀ (y ∷ []))
      η = ⊗-arr (y ∷ [])

      PE : {z : Obₘ} → UR.Hom (⊗₀ (y ∷ [])) z ≃ UR.Hom y z
      PE {z} = (λ f → f UR.∘ η) , ⊗-arr-univ (y ∷ []) {Θ = []} {Ξ = []}

      ε : UR.Hom (⊗₀ (y ∷ [])) y
      ε = Equiv.from PE UR.id

      invl : ε UR.∘ η ≡ UR.id
      invl = Equiv.ε PE UR.id

      invr : η UR.∘ ε ≡ UR.id
      invr = Equiv.injective PE
        ( (η UR.∘ ε) UR.∘ η ≡⟨ sym (UR.assoc η ε η) ⟩
          η UR.∘ (ε UR.∘ η) ≡⟨ ap (η UR.∘_) invl ⟩
          η UR.∘ UR.id      ≡⟨ UR.idr η ⟩
          η                 ≡˘⟨ UR.idl η ⟩
          UR.id UR.∘ η      ∎ )

  -- Split essentially surjective: y is hit by the singleton context [y].
  Reindex-eso : is-split-eso Reindex
  Reindex-eso y = (y ∷ []) , sing-iso y

  -- Hence the comparison functor is an equivalence of categories.
  Reindex-is-equivalence : is-equivalence Reindex
  Reindex-is-equivalence = ff+split-eso→is-equivalence Reindex-ff Reindex-eso
