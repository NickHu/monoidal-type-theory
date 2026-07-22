open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)
open import Cat.Univalent using (is-category; module Univalent)

open import Multicategory
open import Multicategory.Unary

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
  -- Representability is a proposition (assuming the underlying category is
  -- univalent).  Two representations of the same context are equal: the two
  -- universal arrows induce a canonical iso between the two tensor objects,
  -- univalence turns that iso into a path, the arrow lies over it, and the
  -- universality component is a proposition.
  -- ==========================================================================

  -- Restrict a unary map out of t (in context) to a multimap out of Γ, by
  -- plugging in the universal arrow u.  This is the `_∘ₘ u` half of the
  -- universality equivalence, with the trailing `[]` (from `_∘ₘ_` at Θ=Ξ=[])
  -- absorbed via ++-idr.
  restr : ∀ {Γ t} (u : Homₘ Γ t) {z} → Homₘ (t ∷ []) z → Homₘ Γ z
  restr {Γ} u {z} k =
    subst (λ Ω → Homₘ Ω z) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} k u)

  -- Universality packaged as an equivalence Homₘ (t ∷ []) z ≃ Homₘ Γ z.  Its
  -- forward map is (definitionally) `restr u`.
  restrE : ∀ {Γ t} (u : Homₘ Γ t) (pu : is-universal u) {z}
         → Homₘ (t ∷ []) z ≃ Homₘ Γ z
  restrE {Γ} {t} u pu {z} =
    ( (λ (f : Homₘ (t ∷ []) z) → _∘ₘ_ {Θ = []} {Ξ = []} f u) , pu {Θ = []} {Ξ = []} {z} )
    ∙e path→equiv (ap (λ Ω → Homₘ Ω z) (++-idr Γ))

  -- Plugging a subst'd morphism = subst of the plug (naturality of _∘ₘ_ in its
  -- second argument under object-path transport).  [same as Strictification.]
  ∘ₘ-substr : ∀ {B B'} {w z} (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
            → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) p m)
              ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) p (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  ∘ₘ-substr {B} {w = w} {z} a p m =
    J (λ B'' q → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) q m)
                 ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) q (_∘ₘ_ {Θ = []} {Ξ = []} a m))
      (ap (_∘ₘ_ {Θ = []} {Ξ = []} a) (transport-refl m) ∙ sym (transport-refl _))
      p

  -- The list coherence `++-assoc Γ [] [] ≡ ap (_++ []) (++-idr Γ)`, proven by
  -- induction on Γ (so we do NOT need Obₘ to be a set: in a univalent category
  -- Obₘ is only a groupoid).
  ++-assoc-idr : (Γ : List Obₘ) → ++-assoc Γ [] [] ≡ (λ i → [] ++ (++-idr Γ i) ++ [])
  ++-assoc-idr []      = refl
  ++-assoc-idr (a ∷ Γ) = ap (ap (a ∷_)) (++-assoc-idr Γ)

  -- `restr u` is natural under unary post-composition (associativity of the
  -- plug at the generators).  Ports Strictification.restrict-nat to an
  -- arbitrary universal arrow u, using ++-assoc-idr in place of Obₘ-set.
  plug-nat : ∀ {Γ t} (u : Homₘ Γ t) {w z}
             (a : Homₘ (w ∷ []) z) (φ : Homₘ (t ∷ []) w)
           → restr u (_∘ₘ_ {Θ = []} {Ξ = []} a φ)
             ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
                 (_∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ))
  plug-nat {Γ} {t} u {w} {z} a φ = ap (subst (λ Ω → Homₘ Ω z) (++-idr Γ)) step
    where
      aφ : Homₘ (t ∷ []) z
      aφ = _∘ₘ_ {Θ = []} {Ξ = []} a φ
      φσ : Homₘ (Γ ++ []) w
      φσ = _∘ₘ_ {Θ = []} {Ξ = []} φ u
      Y : Homₘ ((Γ ++ []) ++ []) z
      Y = _∘ₘ_ {Θ = []} {Ξ = []} a φσ
      X : Homₘ (Γ ++ []) z
      X = _∘ₘ_ {Θ = []} {Ξ = []} aφ u
      e0 : _∘ₘ_ {Θ = []} {Ξ = []}
             (subst (λ Ω → Homₘ Ω z) (slot-unbury [] [] t [] []) aφ) u ≡ X
      e0 = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q u) (transport-refl aφ)
      pp : PathP (λ i → Homₘ ([] ++ (++-idr Γ i) ++ []) z) Y X
      pp = subst (λ p → PathP (λ i → Homₘ (p i) z) Y X) (++-assoc-idr Γ)
             (symP (assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} a φ u) ▷ e0)
      step : X ≡ _∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ)
      step =
        X                                                   ≡⟨ sym (from-pathp pp) ⟩
        subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) (++-idr Γ) Y   ≡˘⟨ ∘ₘ-substr a (++-idr Γ) φσ ⟩
        _∘ₘ_ {Θ = []} {Ξ = []} a (restr u φ)                ∎

  -- Given two universal arrows u : Homₘ Γ t, u' : Homₘ Γ t', the canonical
  -- comparison maps g = restrE.from u' : t → t' and h = restrE.from u : t' → t
  -- (in Unary M) are mutually inverse.  This lemma gives h ∘ g = id; swapping
  -- (u,u') gives g ∘ h = id.
  retract : ∀ {Γ t t'} (u : Homₘ Γ t) (pu : is-universal u)
              (u' : Homₘ Γ t') (pu' : is-universal u')
          → _∘ₘ_ {Θ = []} {Ξ = []}
              (Equiv.from (restrE u' pu') u) (Equiv.from (restrE u pu) u') ≡ idₘ
  retract {Γ} {t} {t'} u pu u' pu' =
    Equiv.injective (restrE u pu) {x = _∘ₘ_ {Θ = []} {Ξ = []} h′ g} {y = idₘ}
      ( restr u (_∘ₘ_ {Θ = []} {Ξ = []} h′ g)
          ≡⟨ plug-nat u h′ g ⟩
        subst (λ Ω → Homₘ Ω t) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} h′ (restr u g))
          ≡⟨ ap (λ w → subst (λ Ω → Homₘ Ω t) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} h′ w))
                (Equiv.ε (restrE u pu) u') ⟩
        subst (λ Ω → Homₘ Ω t) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} h′ u')
          ≡⟨ Equiv.ε (restrE u' pu') u ⟩
        u
          ≡˘⟨ from-pathp (idₘr u) ⟩
        restr u idₘ ∎ )
    where
      g  = Equiv.from (restrE u pu) u'
      h′ = Equiv.from (restrE u' pu') u

  module _ (cat : is-category (Unary M)) where
    private module UC = Univalent cat
    open UC using (iso→path ; iso→path-id ; J-iso ; _≅_ ; make-iso ; to)

    -- Transport of a multimap along a codomain path = plugging the induced iso.
    subst-cod : ∀ {Γ} {a b} (ι : a ≅ b) (m : Homₘ Γ a)
              → subst (λ z → Homₘ Γ z) (iso→path ι) m
                ≡ subst (λ Ω → Homₘ Ω b) (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} (ι .to) m)
    subst-cod {Γ} ι m =
      J-iso (λ b' i → subst (λ z → Homₘ Γ z) (iso→path i) m
                      ≡ subst (λ Ω → Homₘ Ω b') (++-idr Γ) (_∘ₘ_ {Θ = []} {Ξ = []} (i .to) m))
        ( ap (λ r → subst (λ z → Homₘ Γ z) r m) iso→path-id
        ∙ transport-refl m
        ∙ sym (from-pathp (idₘr m)) )
        ι

    Representation-is-prop : (Γ : List Obₘ) → is-prop (Representation Γ)
    Representation-is-prop Γ (t , u , pu) (t' , u' , pu') =
      Σ-pathp p (Σ-pathp u-pp uu-pp)
      where
        g  = Equiv.from (restrE u pu) u'
        h′ = Equiv.from (restrE u' pu') u
        isom : t ≅ t'
        isom = make-iso g h′ (retract u' pu' u pu) (retract u pu u' pu')
        p : t ≡ t'
        p = iso→path isom
        u-pp : PathP (λ i → Homₘ Γ (p i)) u u'
        u-pp = to-pathp (subst-cod isom u ∙ Equiv.ε (restrE u pu) u')
        uu-pp : PathP (λ i → is-universal (u-pp i)) pu pu'
        uu-pp = is-prop→pathp (λ i → is-universal-is-prop (u-pp i)) pu pu'

    is-representable-is-prop : is-prop is-representable
    is-representable-is-prop = Π-is-hlevel 1 (λ Γ → Representation-is-prop Γ)
