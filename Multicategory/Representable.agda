open import 1Lab.Prelude
open import Cat.Base
open import Cat.Functor.Hom using (Hom-from)
open import Cat.Functor.Naturality
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import Multicategory.Unary
import Cat.Functor.Hom.Representable as CFHR

module Multicategory.Representable where

module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M

  -- A multimorphism u : Homₘ Γ t is *universal* (opcartesian) when plugging it
  -- into a slot is an equivalence on hom-sets, in every context.  Universal
  -- arrows exhibit t as "the tensor ⊗Γ": maps out of t (in context) are the
  -- same as maps out of Γ.
  is-universal : ∀ {Γ t} (u : Homₘ Γ t) → Type (o ⊔ h)
  is-universal {Γ} {t} u =
    ∀ {Θ Ξ z} → is-equiv (λ (f : Homₘ (Θ ++ t ∷ Ξ) z)
                          → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} f u)

  is-universal-is-prop : ∀ {Γ t} (u : Homₘ Γ t) → is-prop (is-universal u)
  is-universal-is-prop u = hlevel 1

  -- A representation of Γ is a tensor object together with a universal arrow.
  Representation : List Obₘ → Type (o ⊔ h)
  Representation Γ = Σ[ t ∈ Obₘ ] Σ[ u ∈ Homₘ Γ t ] is-universal u

  -- The multicategory is representable when every context has a representation.
  is-representable : Type (o ⊔ h)
  is-representable = (Γ : List Obₘ) → Representation Γ

  module _ (rep : is-representable) where
    -- The tensor of a context, and its universal arrow.
    ⊗ : List Obₘ → Obₘ
    ⊗ Γ = rep Γ .fst

    ⊗-arr : (Γ : List Obₘ) → Homₘ Γ (⊗ Γ)
    ⊗-arr Γ = rep Γ .snd .fst

    ⊗-arr-universal : (Γ : List Obₘ) → is-universal (⊗-arr Γ)
    ⊗-arr-universal Γ = rep Γ .snd .snd

  -- ==========================================================================
  -- Homₘ Γ - is a functor on the unary category, and a universal arrow makes
  -- its tensor a corepresenting object for it.  Uniqueness of representations
  -- is then 1lab's uniqueness of corepresenting objects.
  -- ==========================================================================

  -- Restrict a unary map out of w (in context) to a multimap out of Γ, by
  -- plugging in an arbitrary multimap u : Homₘ Γ w (universality NOT
  -- required), with the trailing `[]` (from `_∘ₘ_` at Θ=Ξ=[]) absorbed via
  -- ++-idr.  This is the functorial action of Homₘ Γ - along u, and — when u
  -- is universal — one half of the universality equivalence.
  restr : ∀ {Γ w} (u : Homₘ Γ w) {z} → Homₘ (w ∷ []) z → Homₘ Γ z
  restr {Γ} u {z} k =
    subst (λ Ω → Homₘ Ω z) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} k u)

  -- Universality packaged as an equivalence Homₘ (t ∷ []) z ≃ Homₘ Γ z.  Its
  -- forward map is (definitionally) `restr u`.
  restrE : ∀ {Γ t} (u : Homₘ Γ t) (pu : is-universal u) {z}
         → Homₘ (t ∷ []) z ≃ Homₘ Γ z
  restrE {Γ} {t} u pu {z} =
    ( (λ (f : Homₘ (t ∷ []) z) → _∘ₘ_ {Θ = []} {Ξ = []} f u) , pu {Θ = []} {Ξ = []} {z} )
    ∙e path→equiv (ap (λ Ω → Homₘ Ω z) (++-idr Γ))

  -- The unary-shaped instance of ∘ₘ-subst, used pervasively downstream.
  ∘ₘ-substr : ∀ {B B'} {w z} (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
            → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) p m)
              ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) p (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  ∘ₘ-substr a p m =
      ap (λ k → _∘ₘ_ {Θ = []} {Ξ = []} k (subst _ p m)) (sym (transport-refl a))
    ∙ ∘ₘ-subst M refl refl p a m

  -- `restr u` is natural under unary post-composition — i.e. functoriality of
  -- Homₘ Γ - (universality of u again NOT required; this is assocₘ at the
  -- generators, with the boundary reconciled by the spine lemma ++-assoc-nil
  -- instead of any set-level assumption on Obₘ).
  plug-nat : ∀ {Γ w} (u : Homₘ Γ w) {v z}
             (a : Homₘ (v ∷ []) z) (φ : Homₘ (w ∷ []) v)
           → restr u (_∘ₘ_ {Θ = []} {Ξ = []} a φ)
             ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
                 (_∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ))
  plug-nat {Γ} {w} u {v} {z} a φ = ap (subst (λ Ω → Homₘ Ω z) (++-idr Γ)) step
    where
      aφ : Homₘ (w ∷ []) z
      aφ = _∘ₘ_ {Θ = []} {Ξ = []} a φ
      φσ : Homₘ (Γ ++ []) v
      φσ = _∘ₘ_ {Θ = []} {Ξ = []} φ u
      Y : Homₘ ((Γ ++ []) ++ []) z
      Y = _∘ₘ_ {Θ = []} {Ξ = []} a φσ
      X : Homₘ (Γ ++ []) z
      X = _∘ₘ_ {Θ = []} {Ξ = []} aφ u
      e0 : _∘ₘ_ {Θ = []} {Ξ = []}
             (subst (λ Ω → Homₘ Ω z) (slot-unbury [] [] w [] []) aφ) u ≡ X
      e0 = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q u) (transport-refl aφ)
      pp : PathP (λ i → Homₘ ([] ++ (++-idr Γ i) ++ []) z) Y X
      pp = subst (λ p → PathP (λ i → Homₘ (p i) z) Y X) (++-assoc-nil Γ [])
             (symP (assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} a φ u) ▷ e0)
      step : X ≡ _∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ)
      step =
        X                                                   ≡⟨ sym (from-pathp pp) ⟩
        subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) (++-idr Γ) Y   ≡˘⟨ ∘ₘ-substr a (++-idr Γ) φσ ⟩
        _∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ)                ∎

  -- Homₘ Γ - as a functor Unary M → Sets: the identity and composition laws
  -- are idₘr and plug-nat.
  HomΓ : List Obₘ → Functor (Unary M) (Sets h)
  HomΓ Γ .Functor.F₀ z    = el (Homₘ Γ z) Homₘ-set
  HomΓ Γ .Functor.F₁ a m  = restr m a
  HomΓ Γ .Functor.F-id    = funext λ m → from-pathp (idₘr m)
  HomΓ Γ .Functor.F-∘ a b = funext λ m → plug-nat m a b

  private
    module CR = CFHR {C = Unary M}
  open CR using (Corepresentation; Corepresentation-is-prop)
  open Corepresentation
  open _=>_ using (η)

  -- A universal arrow u : Homₘ Γ t exhibits t as a corepresenting object for
  -- Homₘ Γ -: the natural isomorphism Hom (t, -) ≅ Homₘ Γ - is restr u, with
  -- naturality again plug-nat.
  Rep→Corep : ∀ {Γ t} (u : Homₘ Γ t) (pu : is-universal u)
            → Corepresentation (HomΓ Γ)
  Rep→Corep {Γ} {t} u pu .corep = t
  Rep→Corep {Γ} {t} u pu .corepresents = to-natural-iso mk ni⁻¹
    where
      mk : make-natural-iso (Hom-from (Unary M) t) (HomΓ Γ)
      mk .make-natural-iso.eta z k      = restr u k
      mk .make-natural-iso.inv z        = Equiv.from (restrE u pu)
      mk .make-natural-iso.eta∘inv z    = funext λ m → Equiv.ε (restrE u pu) m
      mk .make-natural-iso.inv∘eta z    = funext λ k → Equiv.η (restrE u pu) k
      mk .make-natural-iso.natural x y f = funext λ k → sym (plug-nat u f k)

  -- ==========================================================================
  -- Representability is a proposition when the multicategory is univalent:
  -- the object-and-arrow part is uniqueness of corepresenting objects
  -- (Cat.Functor.Hom.Representable), and universality is a proposition.
  -- ==========================================================================
  module _ (cat : is-multicategory M) where
    Representation-is-prop : (Γ : List Obₘ) → is-prop (Representation Γ)
    Representation-is-prop Γ (t , u , pu) (t' , u' , pu') =
      Σ-pathp objs (Σ-pathp u-pp uu-pp)
      where
        q : Rep→Corep u pu ≡ Rep→Corep u' pu'
        q = Corepresentation-is-prop cat (Rep→Corep u pu) (Rep→Corep u' pu')
        objs : t ≡ t'
        objs = ap corep q
        -- The arrow over the object path: evaluate the corepresentation's
        -- inverse leg at idₘ (giving restr _ idₘ), then peel restr _ idₘ = _
        -- at both ends with idₘr.
        u-pp0 : PathP (λ i → Homₘ Γ (objs i)) (restr u idₘ) (restr u' idₘ)
        u-pp0 i = Isoⁿ.from (q i .corepresents) .η (objs i) idₘ
        u-pp : PathP (λ i → Homₘ Γ (objs i)) u u'
        u-pp = sym (from-pathp (idₘr u)) ◁ u-pp0 ▷ from-pathp (idₘr u')
        uu-pp : PathP (λ i → is-universal (u-pp i)) pu pu'
        uu-pp = is-prop→pathp (λ i → is-universal-is-prop (u-pp i)) pu pu'

    is-representable-is-prop : is-prop is-representable
    is-representable-is-prop = Π-is-hlevel 1 (λ Γ → Representation-is-prop Γ)
