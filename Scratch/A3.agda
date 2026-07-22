module Scratch.A3 where

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory

-- A3: alternative formulations of the Premulticategory laws.
--
-- Proposal: replace the inner `subst` in assocₘ/interchangeₘ by
-- quantification over ANY morphism lying over the reshaping path
-- (a "PathP-graph" formulation).  This is subst-free, symmetric in
-- consumption, and interderivable with the current fields.

module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M

  -- ── Alternative assocₘ, derived FROM the current field.
  assocₘ-alt : ∀ {Θ Ξ Φ Ψ Ρ} {x y z}
      (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ (Φ ++ y ∷ Ψ) x) (h : Homₘ Ρ y)
      (k : Homₘ ((Θ ++ Φ) ++ y ∷ (Ψ ++ Ξ)) z)
    → PathP (λ i → Homₘ (slot-unbury Θ Φ y Ψ Ξ i) z) (f ∘ₘ g) k
    → PathP (λ i → Homₘ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
        (_∘ₘ_ {Θ = Θ ++ Φ} {Ξ = Ψ ++ Ξ} k h) (f ∘ₘ (g ∘ₘ h))
  assocₘ-alt {Θ} {Ξ} {Φ} {Ψ} {Ρ} {x} {y} {z} f g h k kp =
    subst (λ k' → PathP (λ i → Homₘ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
                    (_∘ₘ_ {Θ = Θ ++ Φ} {Ξ = Ψ ++ Ξ} k' h) (f ∘ₘ (g ∘ₘ h)))
      (from-pathp kp) (assocₘ f g h)

  -- ── The current field is recovered from the alternative (at the filler),
  -- so the two formulations are interderivable.
  assocₘ-orig : ∀ {Θ Ξ Φ Ψ Ρ} {x y z}
      (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ (Φ ++ y ∷ Ψ) x) (h : Homₘ Ρ y)
    → PathP (λ i → Homₘ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
        (subst (λ Ω → Homₘ Ω z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ₘ g) ∘ₘ h)
        (f ∘ₘ (g ∘ₘ h))
  assocₘ-orig {Θ} {Ξ} {Φ} {Ψ} {y = y} {z = z} f g h =
    assocₘ-alt f g h _
      (transport-filler (λ i → Homₘ (slot-unbury Θ Φ y Ψ Ξ i) z) (f ∘ₘ g))

  -- ── Ergonomics payoff: at degenerate contexts the PathP argument is refl,
  -- so consumers do not pay the `transport-refl` fixup that the subst
  -- formulation forces.  Compare Unary.Precategory.assoc (which needs
  --   `∙ ap … (transport-refl (f ∘ₘ g))`)
  -- and Strictification.restrict-nat's `e0` step.
  unary-assoc' : ∀ {w x y z}
      (f : Homₘ (y ∷ []) z) (g : Homₘ (x ∷ []) y) (h : Homₘ (w ∷ []) x)
    → _∘ₘ_ {Θ = []} {Ξ = []} f (_∘ₘ_ {Θ = []} {Ξ = []} g h)
      ≡ _∘ₘ_ {Θ = []} {Ξ = []} (_∘ₘ_ {Θ = []} {Ξ = []} f g) h
  unary-assoc' f g h = sym (assocₘ-alt f g h _ refl)

  -- ── Alternative interchangeₘ (one direction shown; the other is the same
  -- filler instantiation as assocₘ-orig).  All three reshapes are now
  -- quantified PathPs; the statement has no subst and is left/right
  -- symmetric in how the two plug orders are presented.
  interchangeₘ-alt : ∀ {Θ Μ Κ Γ Δ} {x y z}
      (f : Homₘ (Θ ++ x ∷ Μ ++ y ∷ Κ) z) (g : Homₘ Γ x) (h : Homₘ Δ y)
      (f' : Homₘ ((Θ ++ x ∷ Μ) ++ y ∷ Κ) z)
    → PathP (λ i → Homₘ (interchange-slot₀ Θ x Μ y Κ i) z) f f'
    → (fg' : Homₘ ((Θ ++ Γ ++ Μ) ++ y ∷ Κ) z)
    → PathP (λ i → Homₘ (interchange-slot₁ Θ Γ Μ y Κ i) z) (f ∘ₘ g) fg'
    → (fh' : Homₘ (Θ ++ x ∷ (Μ ++ Δ ++ Κ)) z)
    → PathP (λ i → Homₘ (interchange-slot₂ Θ x Μ Δ Κ i) z)
        (_∘ₘ_ {Θ = Θ ++ x ∷ Μ} {Ξ = Κ} f' h) fh'
    → PathP (λ i → Homₘ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
        (_∘ₘ_ {Θ = Θ ++ Γ ++ Μ} {Ξ = Κ} fg' h)
        (_∘ₘ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ} fh' g)
  interchangeₘ-alt {Θ} {Μ} {Κ} {Γ} {Δ} {x} {y} {z} f g h f' fp fg' fgp fh' fhp =
    subst₂ (λ a b → PathP (λ i → Homₘ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
                      (_∘ₘ_ {Θ = Θ ++ Γ ++ Μ} {Ξ = Κ} a h)
                      (_∘ₘ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ} b g))
      (from-pathp fgp)
      ( ap (subst (λ Ω → Homₘ Ω z) (interchange-slot₂ Θ x Μ Δ Κ))
           (ap (λ w → _∘ₘ_ {Θ = Θ ++ x ∷ Μ} {Ξ = Κ} w h) (from-pathp fp))
      ∙ from-pathp fhp )
      (interchangeₘ f g h)

  -- ── And the current interchange field is recovered from the alternative
  -- (using only interchangeₘ-alt as a black box), so interchange is also
  -- fully interderivable.
  interchangeₘ-orig : ∀ {Θ Μ Κ Γ Δ} {x y z}
      (f : Homₘ (Θ ++ x ∷ Μ ++ y ∷ Κ) z) (g : Homₘ Γ x) (h : Homₘ Δ y)
    → PathP (λ i → Homₘ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
        (subst (λ Ω → Homₘ Ω z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ₘ g) ∘ₘ h)
        (subst (λ Ω → Homₘ Ω z) (interchange-slot₂ Θ x Μ Δ Κ)
          (subst (λ Ω → Homₘ Ω z) (interchange-slot₀ Θ x Μ y Κ) f ∘ₘ h) ∘ₘ g)
  interchangeₘ-orig {Θ} {Μ} {Κ} {Γ} {Δ} {x} {y} {z} f g h =
    interchangeₘ-alt f g h
      _ (transport-filler (λ i → Homₘ (interchange-slot₀ Θ x Μ y Κ i) z) f)
      _ (transport-filler (λ i → Homₘ (interchange-slot₁ Θ Γ Μ y Κ i) z) (f ∘ₘ g))
      _ (transport-filler (λ i → Homₘ (interchange-slot₂ Θ x Μ Δ Κ i) z)
           (_∘ₘ_ {Θ = Θ ++ x ∷ Μ} {Ξ = Κ}
             (subst (λ Ω → Homₘ Ω z) (interchange-slot₀ Θ x Μ y Κ) f) h))

  -- ── The homogeneous (fully-subst) formulation is also interderivable,
  -- one `from-pathp` away; kept here for reference.
  assocₘ-hom : ∀ {Θ Ξ Φ Ψ Ρ} {x y z}
      (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ (Φ ++ y ∷ Ψ) x) (h : Homₘ Ρ y)
    → subst (λ Ω → Homₘ Ω z) (assocₘ-boundary Θ Φ Ρ Ψ Ξ)
        (subst (λ Ω → Homₘ Ω z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ₘ g) ∘ₘ h)
      ≡ f ∘ₘ (g ∘ₘ h)
  assocₘ-hom f g h = from-pathp (assocₘ f g h)
