open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Data.Nat
open import Data.Fin.Base
open import Data.Fin.Extra
open import Data.Vec.Base hiding (_++_)
open import Data.Vec.Extra
open import Data.Vec.Splice

module Multicategory.Instances where

-- Every category is (trivially) a multicategory: the only inhabited
-- multihomsets are the unary ones, which agree with the original Homs.
underlying-multicategory : ∀ {o h} → Precategory o h → Premulticategory o h
underlying-multicategory C = M where
  open Precategory C
  open Premulticategory

  M : Premulticategory _ _
  M .Obₘ = Ob

  M .Homₘ {zero} _ _ = Lift _ ⊥
  M .Homₘ {suc zero} Γ y = Hom (head Γ) y
  M .Homₘ {suc (suc _)} _ _ = Lift _ ⊥

  M .Homₘ-set {zero} = hlevel 2
  M .Homₘ-set {suc zero} = Hom-set _ _
  M .Homₘ-set {suc (suc _)} = hlevel 2

  M .idₘ = id

  M ._∘ₘ[_]_ {suc zero} {suc zero} {_ ∷ []} {_ ∷ []} f fzero g = f ∘ g
  M ._∘ₘ[_]_ {suc zero} {suc zero} f (fin (suc _) ⦃ b ⦄) g =
    absurd (¬suc≤0 (≤-peel b))
  M ._∘ₘ[_]_ {zero} {suc zero} f i g = absurd (lower g)
  M ._∘ₘ[_]_ {suc (suc _)} {suc zero} f i g = absurd (lower g)
  M ._∘ₘ[_]_ {_} {zero} f i g = absurd (Fin-absurd i)
  M ._∘ₘ[_]_ {_} {suc (suc _)} f i g = absurd (lower f)

  M .idₘl[_]_ {zero} {_ ∷ []} fzero f = idr f
  M .idₘl[_]_ {zero} (fin (suc _) ⦃ b ⦄) f = absurd (¬suc≤0 (≤-peel b))
  M .idₘl[_]_ {suc _} i f = absurd (lower f)

  M .idₘr {suc zero} {_ ∷ []} f = idl f
  M .idₘr {zero} f = absurd (lower f)
  M .idₘr {suc (suc _)} f = absurd (lower f)

  M .assocₘ {zero} {zero} {suc zero} {z ∷ []} {y ∷ []} {x ∷ []} fzero fzero f g h =
    (f ∘ g) ∘ subst (Hom x) (sym (lookup-splice (z ∷ []) fzero (y ∷ []) fzero)) h
      ≡⟨ ap ((f ∘ g) ∘_) (transport-refl h) ⟩
    (f ∘ g) ∘ h
      ≡˘⟨ assoc f g h ⟩
    f ∘ (g ∘ h) ∎
  M .assocₘ {zero} {zero} {suc zero} fzero (fin (suc _) ⦃ b ⦄) f g h =
    absurd (¬suc≤0 (≤-peel b))
  M .assocₘ {zero} {zero} {suc zero} (fin (suc _) ⦃ b ⦄) j f g h =
    absurd (¬suc≤0 (≤-peel b))
  M .assocₘ {zero} {zero} {zero} i j f g h = absurd (lower h)
  M .assocₘ {zero} {zero} {suc (suc _)} i j f g h = absurd (lower h)
  M .assocₘ {zero} {suc _} i j f g h = absurd (lower g)
  M .assocₘ {suc _} i j f g h = absurd (lower f)

  M .interchangeₘ _ _ _ f _ _ = absurd (lower f)
