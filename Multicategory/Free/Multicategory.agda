open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties
open import Data.Set.Coequaliser

open import Multicategory
open import Multicategory.Free

module Multicategory.Free.Multicategory {o h} (G : Multigraph o h) where

-- The syntactic multicategory FMonCat G (Theorem 2.4.6/2.4.10): hom-sets are
-- terms modulo the β/η congruence; composition is substitution at the
-- canonical split, descended through the quotient; the four laws descend
-- from the Tm-level laws (Identity, Assoc, Interchange) — since those hold
-- as paths, descent is `inc` applied under the interval, never a quotient
-- of the congruence.

open import Multicategory.Free.SplitLemmas G
open import Multicategory.Free.Identity G
open import Multicategory.Free.Assoc G
open import Multicategory.Free.Interchange G
open import Multicategory.Free.Congruence G

private variable
  x y z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Λ Μ Κ Φ : Ctx
  As : List (Multigraph.Ob G)

-- Hom-sets: terms modulo β/η.
Homᶠ : Ctx → Ty → Type (o ⊔ h)
Homᶠ Γ z = Tm Γ z / _≈_

idᶠ : Homᶠ (z ∷ []) z
idᶠ = inc var

-- Composition: substitution at the canonical split, descended.
infixr 9 _∘ᶠ_
_∘ᶠ_ : Homᶠ (Θ ++ x ∷ Ξ) z → Homᶠ Γ x → Homᶠ (Θ ++ Γ ++ Ξ) z
_∘ᶠ_ {Θ = Θ} {x = x} {Ξ = Ξ} =
  Quot-op₂ (λ t → ≈-refl) (λ g → ≈-refl)
    (λ t g → sub (split-here Θ x Ξ) t g)
    (λ t t' g g' e₁ e₂ →
      ≈-trans (sub-≈ʳ (split-here Θ x Ξ) e₁ g)
              (sub-≈ˡ (split-here Θ x Ξ) t' e₂))

-- On class representatives, composition is definitionally substitution:
--   inc t ∘ᶠ inc g = inc (sub (split-here Θ x Ξ) t g).

-- inc applied under the interval (pinning the quotient's implicits).
incᵖ : {t t' : Tm Γ z} → t ≡ t' → Path (Homᶠ Γ z) (inc t) (inc t')
incᵖ p i = inc (p i)

incᵖᵖ : {p : Γ ≡ Δ} {t : Tm Γ z} {t' : Tm Δ z}
      → PathP (λ i → Tm (p i) z) t t' → PathP (λ i → Homᶠ (p i) z) (inc t) (inc t')
incᵖᵖ P i = inc (P i)

-- Left identity: sub-id at the canonical split, whose split-path is refl.
idᶠl : (f : Homᶠ (Θ ++ x ∷ Ξ) z) → f ∘ᶠ idᶠ ≡ f
idᶠl {Θ = Θ} {x = x} {Ξ = Ξ} {z = z} =
  Coeq-elim-prop (λ f → squash (f ∘ᶠ idᶠ) f)
    λ t → incᵖ (tm-over (split-path-here Θ x Ξ) (sub-id (split-here Θ x Ξ) t))

-- Right identity: the var clause of sub is a cast, so this is a filler.
idᶠr : (f : Homᶠ Γ z)
     → PathP (λ i → Homᶠ (++-idr Γ i) z) (_∘ᶠ_ {Θ = []} idᶠ f) f
idᶠr {Γ = Γ} {z = z} =
  Coeq-elim-prop
    (λ f → PathP-is-hlevel' 1 squash (_∘ᶠ_ {Θ = []} idᶠ f) f)
    λ g → symP (incᵖᵖ (cast-filler (sym (++-idr Γ)) g))

-- subst through the quotient is cast under inc.
subst-inc : (p : Γ ≡ Δ) (t : Tm Γ z)
          → subst (λ Ω → Homᶠ Ω z) p (inc t) ≡ inc (cast p t)
subst-inc p t = from-pathp (incᵖᵖ (cast-filler p t))

-- The canonical split of the exposed slot, over each of the record's
-- boundary transports (all cons-by-cons; bases are SplitLemmas coherences
-- or definitional).
unbury-split : ∀ (Θ Φ : Ctx) (y : Ty) (Ψ Ξ : Ctx)
  → PathP (λ i → Split y (Θ ++ Φ) (slot-unbury Θ Φ y Ψ Ξ i) (Ψ ++ Ξ))
      (split-++ʳ Θ (split-++ˡ (split-here Φ y Ψ) Ξ))
      (split-here (Θ ++ Φ) y (Ψ ++ Ξ))
unbury-split []      Φ y Ψ Ξ = split-here-++ˡ Φ y Ψ Ξ
unbury-split (a ∷ Θ) Φ y Ψ Ξ i = there (unbury-split Θ Φ y Ψ Ξ i)

slot₁-split : ∀ (Θ Γ Μ : Ctx) (y : Ty) (Κ : Ctx)
  → PathP (λ i → Split y (Θ ++ Γ ++ Μ) (interchange-slot₁ Θ Γ Μ y Κ i) Κ)
      (split-++ʳ Θ (split-++ʳ Γ (split-here Μ y Κ)))
      (split-here (Θ ++ Γ ++ Μ) y Κ)
slot₁-split []      Γ Μ y Κ = split-here-++ʳ Γ Μ y Κ
slot₁-split (a ∷ Θ) Γ Μ y Κ i = there (slot₁-split Θ Γ Μ y Κ i)

slot₀-split : ∀ (Θ : Ctx) (x : Ty) (Μ : Ctx) (y : Ty) (Κ : Ctx)
  → PathP (λ i → Split y (Θ ++ x ∷ Μ) (interchange-slot₀ Θ x Μ y Κ i) Κ)
      (split-behind (split-here Θ x (Μ ++ y ∷ Κ)) (split-here Μ y Κ))
      (split-here (Θ ++ x ∷ Μ) y Κ)
slot₀-split []      x Μ y Κ = refl
slot₀-split (a ∷ Θ) x Μ y Κ i = there (slot₀-split Θ x Μ y Κ i)

-- Associativity descends: reconcile the record's boundary transports with
-- the composite split via unbury-split, then apply sub-assoc under inc.
assocᶠ : ∀ {Θ Ξ Φ Ψ Ρ x y z}
         (f : Homᶠ (Θ ++ x ∷ Ξ) z) (g : Homᶠ (Φ ++ y ∷ Ψ) x) (h : Homᶠ Ρ y)
       → PathP (λ i → Homᶠ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
           (_∘ᶠ_ {Θ = Θ ++ Φ} {Ξ = Ψ ++ Ξ}
             (subst (λ Ω → Homᶠ Ω z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ᶠ g)) h)
           (f ∘ᶠ (g ∘ᶠ h))
assocᶠ {Θ} {Ξ} {Φ} {Ψ} {Ρ} {x} {y} {z} =
  Coeq-elim-prop (λ _ → hlevel 1) λ t →
  Coeq-elim-prop (λ _ → hlevel 1) λ u →
  Coeq-elim-prop (λ _ → hlevel 1) λ v →
  core t u v
  where
    sx = split-here Θ x Ξ
    sy = split-here Φ y Ψ
    U  = slot-unbury Θ Φ y Ψ Ξ

    core : (t : Tm (Θ ++ x ∷ Ξ) z) (u : Tm (Φ ++ y ∷ Ψ) x) (v : Tm Ρ y)
         → PathP (λ i → Homᶠ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
             (_∘ᶠ_ {Θ = Θ ++ Φ} {Ξ = Ψ ++ Ξ}
               (subst (λ Ω → Homᶠ Ω z) U (inc (sub sx t u))) (inc v))
             (inc (sub sx t (sub sy u v)))
    core t u v =
        ( ap (_∘ᶠ inc v) (subst-inc U (sub sx t u))
        ∙ incᵖ (λ i → sub (unbury-split Θ Φ y Ψ Ξ (~ i))
                          (cast-filler U (sub sx t u) (~ i)) v) )
      ◁ incᵖᵖ (sub-assoc sx sy t u v)

-- Interchange descends: reconcile all three boundary transports
-- (slot₀/slot₁/slot₂) with their composite splits, then sub-interchange.
interchangeᶠ : ∀ {Θ Μ Κ Γ Δ x y z}
               (f : Homᶠ (Θ ++ x ∷ Μ ++ y ∷ Κ) z) (g : Homᶠ Γ x) (h : Homᶠ Δ y)
             → PathP (λ i → Homᶠ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
                 (_∘ᶠ_ {Θ = Θ ++ Γ ++ Μ} {Ξ = Κ}
                   (subst (λ Ω → Homᶠ Ω z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ᶠ g)) h)
                 (_∘ᶠ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ}
                   (subst (λ Ω → Homᶠ Ω z) (interchange-slot₂ Θ x Μ Δ Κ)
                     (_∘ᶠ_ {Θ = Θ ++ x ∷ Μ} {Ξ = Κ}
                       (subst (λ Ω → Homᶠ Ω z) (interchange-slot₀ Θ x Μ y Κ) f) h)) g)
interchangeᶠ {Θ} {Μ} {Κ} {Γ} {Δ} {x} {y} {z} =
  Coeq-elim-prop (λ _ → hlevel 1) λ t →
  Coeq-elim-prop (λ _ → hlevel 1) λ u →
  Coeq-elim-prop (λ _ → hlevel 1) λ v →
  core t u v
  where
    sx = split-here Θ x (Μ ++ y ∷ Κ)
    s₂ = split-here Μ y Κ
    S₀ = interchange-slot₀ Θ x Μ y Κ
    S₁ = interchange-slot₁ Θ Γ Μ y Κ
    S₂ = interchange-slot₂ Θ x Μ Δ Κ

    core : (t : Tm (Θ ++ x ∷ Μ ++ y ∷ Κ) z) (u : Tm Γ x) (v : Tm Δ y)
         → PathP (λ i → Homᶠ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
             (_∘ᶠ_ {Θ = Θ ++ Γ ++ Μ} {Ξ = Κ}
               (subst (λ Ω → Homᶠ Ω z) S₁ (inc (sub sx t u))) (inc v))
             (_∘ᶠ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ}
               (subst (λ Ω → Homᶠ Ω z) S₂
                 (_∘ᶠ_ {Θ = Θ ++ x ∷ Μ} {Ξ = Κ}
                   (subst (λ Ω → Homᶠ Ω z) S₀ (inc t)) (inc v))) (inc u))
    core t u v =
        ( ap (_∘ᶠ inc v) (subst-inc S₁ (sub sx t u))
        ∙ incᵖ (λ i → sub (slot₁-split Θ Γ Μ y Κ (~ i))
                          (cast-filler S₁ (sub sx t u) (~ i)) v) )
      ◁ incᵖᵖ (sub-interchange sx s₂ t u v)
      ▷ sym
        ( ap (λ k → _∘ᶠ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ}
                      (subst (λ Ω → Homᶠ Ω z) S₂ (k ∘ᶠ inc v)) (inc u))
             (subst-inc S₀ t)
        ∙ ap (λ k → _∘ᶠ_ {Θ = Θ} {Ξ = Μ ++ Δ ++ Κ}
                      (subst (λ Ω → Homᶠ Ω z) S₂ k) (inc u))
             (incᵖ (λ i → sub (slot₀-split Θ x Μ y Κ (~ i))
                              (cast-filler S₀ t (~ i)) v))
        ∙ ap (_∘ᶠ inc u)
             (subst-inc S₂ (sub (split-behind sx s₂) t v))
        ∙ incᵖ (λ i → sub (split-here-++ˡ Θ x Μ (Δ ++ Κ) (~ i))
                          (cast-filler S₂ (sub (split-behind sx s₂) t v) (~ i)) u) )

-- The syntactic multicategory: the free representable-to-be multicategory
-- on the multigraph G (Theorem 2.4.6's multicategory, β/η-quotiented as in
-- Theorem 2.4.10).
FMonCat : Premulticategory o (o ⊔ h)
FMonCat .Premulticategory.Obₘ = Ty
FMonCat .Premulticategory.Homₘ = Homᶠ
FMonCat .Premulticategory.Homₘ-set = squash
FMonCat .Premulticategory.idₘ = idᶠ
FMonCat .Premulticategory._∘ₘ_ = _∘ᶠ_
FMonCat .Premulticategory.idₘl = idᶠl
FMonCat .Premulticategory.idₘr = idᶠr
FMonCat .Premulticategory.assocₘ = assocᶠ
FMonCat .Premulticategory.interchangeₘ = interchangeᶠ
