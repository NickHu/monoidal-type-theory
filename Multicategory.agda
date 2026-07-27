open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

import ListPath.Solver

module Multicategory where

-- Multicategories: multimorphisms take a list of objects (the context) to a
-- single object.  Contexts are lists, so the only operation on them is _++_;
-- there are no length indices, no Fin, and no splice.  A slot is specified by
-- a decomposition of the list: Θ ++ x ∷ Ξ marks x as the slot, with Θ before
-- it and Ξ after.  The "Pre" in Premulticategory parallels 1lab's
-- Precategory: no univalence is assumed (see is-multicategory in
-- Multicategory.Unary).
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
-- Clause-for-clause identical to the generic list-path solver's `bury`, and
-- aliased to it so solver goals mentioning it are in-vocabulary.
assocₘ-flatten : ∀ {A : Type o} (Φ Ρ Ψ Ξ : List A)
  → Φ ++ Ρ ++ (Ψ ++ Ξ) ≡ (Φ ++ Ρ ++ Ψ) ++ Ξ
assocₘ-flatten {A = A} = ListPath.Solver.NbE.bury A

-- The associativity boundary:
--   (Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ)  ≡  Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ)
assocₘ-boundary : ∀ {A : Type o} (Θ Φ Ρ Ψ Ξ : List A)
  → (Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ) ≡ Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ)
assocₘ-boundary []       Φ Ρ Ψ Ξ = assocₘ-flatten Φ Ρ Ψ Ξ
assocₘ-boundary (a ∷ Θ') Φ Ρ Ψ Ξ = ap (a ∷_) (assocₘ-boundary Θ' Φ Ρ Ψ Ξ)

-- Reassociations for interchange.  f has two slots: Θ ++ x ∷ Μ ++ y ∷ Κ.

-- Expose the second slot y of f's own domain:
--   Θ ++ x ∷ Μ ++ y ∷ Κ  ≡  (Θ ++ x ∷ Μ) ++ y ∷ Κ
-- A plain reassociation.  1lab's ++-assoc is itself cons-by-cons structural
-- (and sym commutes with the cons step definitionally), so this alias has
-- the same reductions as a hand-rolled recursion would.
interchange-slot₀ : ∀ {A : Type o} (Θ : List A) (x : A) (Μ : List A) (y : A) (Κ : List A)
  → Θ ++ x ∷ Μ ++ y ∷ Κ ≡ (Θ ++ x ∷ Μ) ++ y ∷ Κ
interchange-slot₀ Θ x Μ y Κ = sym (++-assoc Θ (x ∷ Μ) (y ∷ Κ))

-- Expose y once x has been replaced by Γ:
--   Θ ++ Γ ++ Μ ++ y ∷ Κ  ≡  (Θ ++ Γ ++ Μ) ++ y ∷ Κ
interchange-slot₁ : ∀ {A : Type o} (Θ Γ Μ : List A) (y : A) (Κ : List A)
  → Θ ++ Γ ++ Μ ++ y ∷ Κ ≡ (Θ ++ Γ ++ Μ) ++ y ∷ Κ
interchange-slot₁ []       Γ Μ y Κ = sym (++-assoc Γ Μ (y ∷ Κ))
interchange-slot₁ (a ∷ Θ') Γ Μ y Κ = ap (a ∷_) (interchange-slot₁ Θ' Γ Μ y Κ)

-- Expose x once y has been replaced by Δ (a plain reassociation):
--   (Θ ++ x ∷ Μ) ++ Δ ++ Κ  ≡  Θ ++ x ∷ (Μ ++ Δ ++ Κ)
interchange-slot₂ : ∀ {A : Type o} (Θ : List A) (x : A) (Μ Δ Κ : List A)
  → (Θ ++ x ∷ Μ) ++ Δ ++ Κ ≡ Θ ++ x ∷ (Μ ++ Δ ++ Κ)
interchange-slot₂ Θ x Μ Δ Κ = ++-assoc Θ (x ∷ Μ) (Δ ++ Κ)

-- (Γ ++ Μ) ++ Δ ++ Κ ≡ Γ ++ (Μ ++ Δ ++ Κ)  (base case of interchangeₘ-boundary;
-- a plain reassociation)
interchange-flatten : ∀ {A : Type o} (Γ Μ Δ Κ : List A)
  → (Γ ++ Μ) ++ Δ ++ Κ ≡ Γ ++ (Μ ++ Δ ++ Κ)
interchange-flatten Γ Μ Δ Κ = ++-assoc Γ Μ (Δ ++ Κ)

-- The interchange boundary:
--   (Θ ++ Γ ++ Μ) ++ Δ ++ Κ  ≡  Θ ++ Γ ++ (Μ ++ Δ ++ Κ)
-- Clause-for-clause identical to the generic list-path solver's flattenˡ at
-- ws := Δ ++ Κ, and aliased to it so solver goals are in-vocabulary.
interchangeₘ-boundary : ∀ {A : Type o} (Θ Γ Μ Δ Κ : List A)
  → (Θ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ)
interchangeₘ-boundary {A = A} Θ Γ Μ Δ Κ =
  ListPath.Solver.NbE.flattenˡ A Θ Γ Μ (Δ ++ Κ)

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

    -- Associativity.  Plugging h into the slot inherited from g requires
    -- exposing that slot via slot-unbury, since list _++_ is not strictly
    -- associative.  (In the representable instance this induces the monoidal
    -- pentagon, but the law itself is plain associativity of plugging.)
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

-- ++-assoc with an empty middle is the reindex of ++-idr.  (Pure list-path
-- spine lemma, shared by Representable and Strictification.)
++-assoc-nil : ∀ {A : Type o} (Γ Ξ : List A)
  → ++-assoc Γ [] Ξ ≡ ap (_++ Ξ) (++-idr Γ)
++-assoc-nil []      Ξ = refl
++-assoc-nil (a ∷ Γ) Ξ = ap (ap (a ∷_)) (++-assoc-nil Γ Ξ)

-- _∘ₘ_ commutes with transporting the prefix, suffix, and argument contexts
-- simultaneously.  No J needed: it is _∘ₘ_ applied under the interval to the
-- transport fillers.  All the one-sided transport-naturality facts the
-- development needs (prefix only, suffix only, argument only) are instances,
-- obtained by specialising the other two paths to refl and cancelling the
-- resulting transport-refl.
module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M

  ∘ₘ-subst : {Θ Θ' Ξ Ξ' Γ Γ' : List Obₘ} {x z : Obₘ}
             (p : Θ ≡ Θ') (q : Ξ ≡ Ξ') (r : Γ ≡ Γ')
             (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
           → _∘ₘ_ {Θ = Θ'} {Ξ = Ξ'}
               (transport (λ i → Homₘ (p i ++ x ∷ q i) z) f)
               (subst (λ Ω → Homₘ Ω x) r g)
             ≡ transport (λ i → Homₘ (p i ++ r i ++ q i) z)
                 (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-subst {x = x} {z = z} p q r f g = sym (from-pathp λ i →
    _∘ₘ_ {Θ = p i} {Ξ = q i}
      (transport-filler (λ j → Homₘ (p j ++ x ∷ q j) z) f i)
      (transport-filler (λ j → Homₘ (r j) x) g i))
