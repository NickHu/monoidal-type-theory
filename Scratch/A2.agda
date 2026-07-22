module Scratch.A2 where

open import 1Lab.Prelude
open import Cat.Base
open import Cat.Functor.Hom using (Hom-from)
open import Cat.Functor.Naturality
open import Cat.Univalent using (is-category)
open import Data.List using (List; []; _∷_; _++_; ++-idr)

open import Multicategory
open import Multicategory.Unary
import Multicategory.Representable as Rep
import Cat.Functor.Hom.Representable as CFHR

-- A2: derive Representable.Representation-is-prop from 1lab's
-- Cat.Functor.Hom.Representable.Corepresentation-is-prop, applied to the
-- covariant functor  z ↦ Homₘ Γ z  :  Unary M → Sets h.

module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M
  open _=>_ using (η)
  private
    module CR = CFHR {C = Unary M}
  open CR using (Corepresentation; Corepresentation-is-prop)
  open Corepresentation

  -- The functor  Homₘ Γ -  (functoriality = plug-nat, already proven).
  HomΓ : List Obₘ → Functor (Unary M) (Sets h)
  HomΓ Γ .Functor.F₀ z = el (Homₘ Γ z) Homₘ-set
  HomΓ Γ .Functor.F₁ {_} {z} a m =
    subst (λ Ω → Homₘ Ω z) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  HomΓ Γ .Functor.F-id = funext λ m → from-pathp (idₘr m)
  HomΓ Γ .Functor.F-∘ a b = funext λ m → Rep.plug-nat M m a b

  -- A universal arrow makes t a corepresenting object for HomΓ.
  module _ {Γ : List Obₘ} {t : Obₘ} (u : Homₘ Γ t) (pu : Rep.is-universal M u) where
    private
      mk : make-natural-iso (Hom-from (Unary M) t) (HomΓ Γ)
      mk .make-natural-iso.eta z k = Rep.restr M u k
      mk .make-natural-iso.inv z = Equiv.from (Rep.restrE M u pu)
      mk .make-natural-iso.eta∘inv z = funext λ m → Equiv.ε (Rep.restrE M u pu) m
      mk .make-natural-iso.inv∘eta z = funext λ k → Equiv.η (Rep.restrE M u pu) k
      mk .make-natural-iso.natural x y f = funext λ k → sym (Rep.plug-nat M u f k)

    Rep→Corep : Corepresentation (HomΓ Γ)
    Rep→Corep .corep = t
    Rep→Corep .corepresents = to-natural-iso mk ni⁻¹

  -- Uniqueness now falls out of the library.
  Representation-is-prop' : (cat : is-category (Unary M)) (Γ : List Obₘ)
                          → is-prop (Rep.Representation M Γ)
  Representation-is-prop' cat Γ (t , u , pu) (t' , u' , pu') =
    Σ-pathp objs (Σ-pathp u-pp uu-pp)
    where
      q : Rep→Corep u pu ≡ Rep→Corep u' pu'
      q = Corepresentation-is-prop cat (Rep→Corep u pu) (Rep→Corep u' pu')
      objs : t ≡ t'
      objs = ap corep q
      -- the arrow-over-path: evaluate the (definitionally transparent)
      -- inverse leg of the corepresentation at idₘ, then peel restr∘idₘ = u.
      u-pp0 : PathP (λ i → Homₘ Γ (objs i))
                (Rep.restr M u idₘ) (Rep.restr M u' idₘ)
      u-pp0 i = Isoⁿ.from (q i .corepresents) .η (objs i) idₘ
      u-pp : PathP (λ i → Homₘ Γ (objs i)) u u'
      u-pp = sym (from-pathp (idₘr u)) ◁ u-pp0 ▷ from-pathp (idₘr u')
      uu-pp : PathP (λ i → Rep.is-universal M (u-pp i)) pu pu'
      uu-pp = is-prop→pathp (λ i → Rep.is-universal-is-prop M (u-pp i)) pu pu'
