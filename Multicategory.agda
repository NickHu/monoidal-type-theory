open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

module Multicategory where

-- A (non-unital) multicategory: multimorphisms take a list of objects (the
-- context) to a single object.  Contexts are lists, so the only operation on
-- them is _++_; there are no length indices, no Fin, and no splice.  A slot is
-- specified by a decomposition of the list: Θ ++ x ∷ Ξ marks x as the slot,
-- with Θ before it and Ξ after.
--
-- Naming convention: x y z are objects (z is the codomain of the outermost
-- morphism); Γ Δ Θ Ξ Φ Ψ Ρ Μ Κ are contexts (lists); f g h are multimorphisms.

private variable
  o h : Level

-- List reassociations underlying the associativity and interchange laws.
-- These are defined by structural recursion (cons-by-cons), NOT by composing
-- _++_-assoc with _∙_, so that a fold over the context — homₘ in the
-- underlying instance, ⊗-context in the representable instance — reduces
-- through them definitionally.  (A _∙_-composed reassociation is an hcomp,
-- which a fold cannot pattern-match through; that is what blocked the laws.)
-- They appear in field types below (a record cannot reference its own
-- where-clause), and are exported so that instances can characterise
-- path→iso (ap ⊗-context/homₘ <path>) for the law transports.

-- Expose a slot buried under an extra prefix:
--   Θ ++ ((Φ ++ x ∷ Ψ) ++ Ξ)  ≡  (Θ ++ Φ) ++ x ∷ (Ψ ++ Ξ)
slot-unbury : ∀ {A : Type o} (Θ Φ : List A) (x : A) (Ψ Ξ : List A)
  → Θ ++ ((Φ ++ x ∷ Ψ) ++ Ξ) ≡ (Θ ++ Φ) ++ x ∷ (Ψ ++ Ξ)
slot-unbury []       Φ x Ψ Ξ = ++-assoc Φ (x ∷ Ψ) Ξ
slot-unbury (a ∷ Θ') Φ x Ψ Ξ = ap (a ∷_) (slot-unbury Θ' Φ x Ψ Ξ)

-- Φ ++ Ρ ++ (Ψ ++ Ξ) ≡ (Φ ++ Ρ ++ Ψ) ++ Ξ  (base case of assocₘ-boundary)
assocₘ-flatten : ∀ {A : Type o} (Φ Ρ Ψ Ξ : List A)
  → Φ ++ Ρ ++ (Ψ ++ Ξ) ≡ (Φ ++ Ρ ++ Ψ) ++ Ξ
assocₘ-flatten []       Ρ Ψ Ξ = sym (++-assoc Ρ Ψ Ξ)
assocₘ-flatten (a ∷ Φ') Ρ Ψ Ξ = ap (a ∷_) (assocₘ-flatten Φ' Ρ Ψ Ξ)

-- The associativity boundary:
--   (Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ)  ≡  Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ)
assocₘ-boundary : ∀ {A : Type o} (Θ Φ Ρ Ψ Ξ : List A)
  → (Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ) ≡ Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ)
assocₘ-boundary []       Φ Ρ Ψ Ξ = assocₘ-flatten Φ Ρ Ψ Ξ
assocₘ-boundary (a ∷ Θ') Φ Ρ Ψ Ξ = ap (a ∷_) (assocₘ-boundary Θ' Φ Ρ Ψ Ξ)

-- Reassociations for interchange.  f has two slots: Θ ++ x ∷ Μ ++ y ∷ Κ.

-- Expose the second slot y of f's own domain:
--   Θ ++ x ∷ Μ ++ y ∷ Κ  ≡  (Θ ++ x ∷ Μ) ++ y ∷ Κ
interchange-slot₀ : ∀ {A : Type o} (Θ : List A) (x : A) (Μ : List A) (y : A) (Κ : List A)
  → Θ ++ x ∷ Μ ++ y ∷ Κ ≡ (Θ ++ x ∷ Μ) ++ y ∷ Κ
interchange-slot₀ []       x Μ y Κ = refl
interchange-slot₀ (a ∷ Θ') x Μ y Κ = ap (a ∷_) (interchange-slot₀ Θ' x Μ y Κ)

-- Expose y once x has been replaced by Γ:
--   Θ ++ Γ ++ Μ ++ y ∷ Κ  ≡  (Θ ++ Γ ++ Μ) ++ y ∷ Κ
interchange-slot₁ : ∀ {A : Type o} (Θ Γ Μ : List A) (y : A) (Κ : List A)
  → Θ ++ Γ ++ Μ ++ y ∷ Κ ≡ (Θ ++ Γ ++ Μ) ++ y ∷ Κ
interchange-slot₁ []       Γ Μ y Κ = sym (++-assoc Γ Μ (y ∷ Κ))
interchange-slot₁ (a ∷ Θ') Γ Μ y Κ = ap (a ∷_) (interchange-slot₁ Θ' Γ Μ y Κ)

-- Expose x once y has been replaced by Δ:
--   (Θ ++ x ∷ Μ) ++ Δ ++ Κ  ≡  Θ ++ x ∷ (Μ ++ Δ ++ Κ)
interchange-slot₂ : ∀ {A : Type o} (Θ : List A) (x : A) (Μ Δ Κ : List A)
  → (Θ ++ x ∷ Μ) ++ Δ ++ Κ ≡ Θ ++ x ∷ (Μ ++ Δ ++ Κ)
interchange-slot₂ []       x Μ Δ Κ = refl
interchange-slot₂ (a ∷ Θ') x Μ Δ Κ = ap (a ∷_) (interchange-slot₂ Θ' x Μ Δ Κ)

-- (Γ ++ Μ) ++ Δ ++ Κ ≡ Γ ++ (Μ ++ Δ ++ Κ)  (base case of interchangeₘ-boundary)
interchange-flatten : ∀ {A : Type o} (Γ Μ Δ Κ : List A)
  → (Γ ++ Μ) ++ Δ ++ Κ ≡ Γ ++ (Μ ++ Δ ++ Κ)
interchange-flatten []       Μ Δ Κ = refl
interchange-flatten (a ∷ Γ') Μ Δ Κ = ap (a ∷_) (interchange-flatten Γ' Μ Δ Κ)

-- The interchange boundary:
--   (Θ ++ Γ ++ Μ) ++ Δ ++ Κ  ≡  Θ ++ Γ ++ (Μ ++ Δ ++ Κ)
interchangeₘ-boundary : ∀ {A : Type o} (Θ Γ Μ Δ Κ : List A)
  → (Θ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ)
interchangeₘ-boundary []       Γ Μ Δ Κ = interchange-flatten Γ Μ Δ Κ
interchangeₘ-boundary (a ∷ Θ') Γ Μ Δ Κ = ap (a ∷_) (interchangeₘ-boundary Θ' Γ Μ Δ Κ)

record Premulticategory (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    Obₘ : Type o
    Homₘ : List Obₘ → Obₘ → Type h
    Homₘ-set : ∀ {Γ z} → is-set (Homₘ Γ z)

    idₘ : ∀ {x} → Homₘ (x ∷ []) x

    -- Plug g into the marked slot of f.  f's domain is Θ ++ x ∷ Ξ; the slot x
    -- is replaced by g's context Γ.
    _∘ₘ_ : ∀ {Θ Ξ Γ} {x z}
        → Homₘ (Θ ++ x ∷ Ξ) z → Homₘ Γ x → Homₘ (Θ ++ Γ ++ Ξ) z

    -- Left identity is homogeneous: [x] ++ Ξ = x ∷ Ξ definitionally, so
    -- plugging idₘ into x's slot leaves the context unchanged.
    idₘl : ∀ {Θ Ξ} {x z} (f : Homₘ (Θ ++ x ∷ Ξ) z) → (f ∘ₘ idₘ) ≡ f

    -- Right identity ranges over ++-idr: [] ++ Γ ++ [] = Γ ++ [].  The empty
    -- decomposition of idₘ's domain is given explicitly (Agda will not invert
    -- _++_ on the concrete singleton x ∷ [] to recover Θ = []).
    idₘr : ∀ {Γ z} (f : Homₘ Γ z)
        → PathP (λ i → Homₘ (++-idr Γ i) z) (_∘ₘ_ {Θ = []} idₘ f) f

    -- Associativity (the pentagon).  Plugging h into the slot inherited from g
    -- requires exposing that slot via slot-unbury, since list _++_ is not
    -- strictly associative.
    assocₘ : ∀ {Θ Ξ Φ Ψ Ρ} {x y z}
        → (f : Homₘ (Θ ++ x ∷ Ξ) z)
        → (g : Homₘ (Φ ++ y ∷ Ψ) x)
        → (h : Homₘ Ρ y)
        → PathP (λ i → Homₘ (assocₘ-boundary Θ Φ Ρ Ψ Ξ i) z)
            (subst (λ Ω → Homₘ Ω z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ₘ g) ∘ₘ h)
            (f ∘ₘ (g ∘ₘ h))

    -- Interchange: plug g and h into the two slots of f, in either order.
    interchangeₘ : ∀ {Θ Μ Κ Γ Δ} {x y z}
        → (f : Homₘ (Θ ++ x ∷ Μ ++ y ∷ Κ) z)
        → (g : Homₘ Γ x)
        → (h : Homₘ Δ y)
        → PathP (λ i → Homₘ (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
            (subst (λ Ω → Homₘ Ω z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ₘ g) ∘ₘ h)
            (subst (λ Ω → Homₘ Ω z) (interchange-slot₂ Θ x Μ Δ Κ)
              (subst (λ Ω → Homₘ Ω z) (interchange-slot₀ Θ x Μ y Κ) f ∘ₘ h) ∘ₘ g)

  infixr 9 _∘ₘ_
