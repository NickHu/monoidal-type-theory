open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Data.List
open import Data.List.Properties

module Multicategory.Instances where

-- Every category is (trivially) a multicategory: the only inhabited
-- multihomsets are the unary ones, which agree with the original Homs.
--
-- Because contexts are lists (no length index), a multihomset Homₘ Γ τ is
-- inhabited only when Γ is a singleton.  When a domain is written Θ ++ x ∷ Ξ
-- with Θ a non-empty variable, the (++) is stuck, so to expose that the list is
-- /not/ a singleton we split on the first two elements of each part.
underlying-multicategory : ∀ {o h} → Precategory o h → Premulticategory o h
underlying-multicategory C = M where
  open Precategory C
  open Premulticategory

  homₘ : List Ob → Ob → Type _
  homₘ []           τ = Lift _ ⊥
  homₘ (x ∷ [])     τ = Hom x τ
  homₘ (x ∷ y ∷ Γ)  τ = Lift _ ⊥

  M : Premulticategory _ _
  M .Obₘ = Ob
  M .Homₘ = homₘ

  M .Homₘ-set {Γ = []}           = hlevel 2
  M .Homₘ-set {Γ = x ∷ []}       = Hom-set _ _
  M .Homₘ-set {Γ = x ∷ y ∷ Γ}    = hlevel 2

  M .idₘ = id

  -- Composition is ordinary composition when both sides are singletons.
  M ._∘ₘ_ {Θ = []}     {Ξ = []}    {Γ = y ∷ []}     f g = f ∘ g
  M ._∘ₘ_ {Θ = []}     {Ξ = []}    {Γ = []}         f g = absurd (lower g)
  M ._∘ₘ_ {Θ = []}     {Ξ = []}    {Γ = _ ∷ _ ∷ _}  f g = absurd (lower g)
  M ._∘ₘ_ {Θ = []}     {Ξ = _ ∷ _}                   f g = absurd (lower f)
  M ._∘ₘ_ {Θ = _ ∷ []}                                f g = absurd (lower f)
  M ._∘ₘ_ {Θ = _ ∷ _ ∷ _}                             f g = absurd (lower f)

  M .idₘl {Θ = []}   {Ξ = []}        f = idr f
  M .idₘl {Θ = []}   {Ξ = _ ∷ _}     f = absurd (lower f)
  M .idₘl {Θ = _ ∷ []}               f = absurd (lower f)
  M .idₘl {Θ = _ ∷ _ ∷ _}            f = absurd (lower f)

  M .idₘr {Γ = []}              f = absurd (lower f)
  M .idₘr {Γ = x ∷ []}          f = idl f
  M .idₘr {Γ = x ∷ y ∷ Γ}       f = absurd (lower f)

  -- Associativity is ordinary associativity when f, g, h are all unary.  The
  -- boundary and slot-unbury reassociations are over empty lists, so they are
  -- definitionally constant (structural recursion); only the subst over the
  -- refl-typed slot-unbury is a stuck transport, cancelled by transport-refl.
  M .assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} {Ρ = w ∷ []}  f g h =
    ap (_∘ h) (transport-refl (f ∘ g)) ∙ sym (assoc f g h)
  M .assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} {Ρ = []}      f g h = absurd (lower h)
  M .assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} {Ρ = _ ∷ _ ∷ _} f g h = absurd (lower h)
  M .assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = _ ∷ _}            f g h = absurd (lower g)
  M .assocₘ {Θ = []} {Ξ = []} {Φ = _ ∷ []}                    f g h = absurd (lower g)
  M .assocₘ {Θ = []} {Ξ = []} {Φ = _ ∷ _ ∷ _}                 f g h = absurd (lower g)
  M .assocₘ {Θ = []} {Ξ = _ ∷ _}                              f g h = absurd (lower f)
  M .assocₘ {Θ = _ ∷ []}                                      f g h = absurd (lower f)
  M .assocₘ {Θ = _ ∷ _ ∷ _}                                   f g h = absurd (lower f)

  -- f's domain Θ ++ x ∷ Μ ++ y ∷ Κ always has ≥ 2 elements, so it is never
  -- inhabited; interchange is vacuous.
  M .interchangeₘ {Θ = []}      {Μ = []}          f g h = absurd (lower f)
  M .interchangeₘ {Θ = []}      {Μ = _ ∷ _}       f g h = absurd (lower f)
  M .interchangeₘ {Θ = _ ∷ []}                     f g h = absurd (lower f)
  M .interchangeₘ {Θ = _ ∷ _ ∷ _}                  f g h = absurd (lower f)
