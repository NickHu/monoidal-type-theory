open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory.Free

module Multicategory.Free.SplitLemmas {o h} (G : Multigraph o h) where

open import Multicategory.Free.Kit G public

-- Lemma pack for the slot-witness datatype Split: computation rules for the
-- view split-++ on canonically weakened splits, coherence of the weakenings
-- split-++ˡ / split-++ʳ with each other and with ++-idr / ++-assoc, and the
-- behaviour of split-path on all of them.  Every path is structural — built
-- cons-by-cons by matching an interval variable under the recursion, never a
-- ∙-composite — following the reassociation discipline of Multicategory.agda.

private variable
  x y z a : Ty
  Γ Δ Θ Ξ Ψ Ρ Λ Μ Κ Γ₁ Γ₂ Γ₃ Δ₁ Ξ₁ Θ₂ : Ctx

-- ==========================================================================
-- Computation rules for split-++: the view of a canonically weakened split
-- is the corresponding branch with trivial bookkeeping.  The step case is
-- split-++-step applied under the interval — exactly why split-++-step
-- exists as a named function.
-- ==========================================================================

split-++-ˡ : (s₁ : Split x Θ Γ₁ Ξ₁) (Γ₂ : Ctx)
           → split-++ Γ₁ {Γ₂ = Γ₂} (split-++ˡ s₁ Γ₂) ≡ on-left s₁ refl refl
split-++-ˡ here       Γ₂ = refl
split-++-ˡ (there s₁) Γ₂ i = split-++-step (split-++-ˡ s₁ Γ₂ i)

split-++-ʳ : (Γ₁ : Ctx) (s₂ : Split x Θ Γ₂ Ξ)
           → split-++ Γ₁ {Γ₂ = Γ₂} (split-++ʳ Γ₁ s₂) ≡ on-right s₂ refl refl
split-++-ʳ []       s₂ = refl
split-++-ʳ (a ∷ Γ₁) s₂ i = split-++-step (split-++-ʳ Γ₁ s₂ i)

-- ==========================================================================
-- Coherence of the weakenings with ++-idr and ++-assoc.
-- ==========================================================================

-- Weakening by the empty suffix is the identity, over ++-idr.
split-++ˡ-idr : (s : Split x Θ Λ Ξ)
              → PathP (λ i → Split x Θ (++-idr Λ i) (++-idr Ξ i))
                      (split-++ˡ s []) s
split-++ˡ-idr (here {Ξ = Ξ}) i = here {Ξ = ++-idr Ξ i}
split-++ˡ-idr (there s)      i = there (split-++ˡ-idr s i)

-- Suffix weakening is associative, over ++-assoc.
split-++ˡ-++ : (s : Split x Θ Λ Ξ) (Γ₂ Γ₃ : Ctx)
             → PathP (λ i → Split x Θ (++-assoc Λ Γ₂ Γ₃ i) (++-assoc Ξ Γ₂ Γ₃ i))
                     (split-++ˡ (split-++ˡ s Γ₂) Γ₃) (split-++ˡ s (Γ₂ ++ Γ₃))
split-++ˡ-++ (here {Ξ = Ξ}) Γ₂ Γ₃ i = here {Ξ = ++-assoc Ξ Γ₂ Γ₃ i}
split-++ˡ-++ (there s)      Γ₂ Γ₃ i = there (split-++ˡ-++ s Γ₂ Γ₃ i)

-- Prefix weakening is associative, over ++-assoc.
split-++ʳ-++ : (Γ₁ Γ₂ : Ctx) (s : Split x Θ Λ Ξ)
             → PathP (λ i → Split x (++-assoc Γ₁ Γ₂ Θ i) (++-assoc Γ₁ Γ₂ Λ i) Ξ)
                     (split-++ʳ (Γ₁ ++ Γ₂) s) (split-++ʳ Γ₁ (split-++ʳ Γ₂ s))
split-++ʳ-++ []       Γ₂ s = refl
split-++ʳ-++ (a ∷ Γ₁) Γ₂ s i = there (split-++ʳ-++ Γ₁ Γ₂ s i)

-- Prefix and suffix weakening commute, over ++-assoc.
split-++ˡʳ-comm : (Γ₁ : Ctx) (s : Split x Θ Λ Ξ) (Γ₂ : Ctx)
                → PathP (λ i → Split x (Γ₁ ++ Θ) (++-assoc Γ₁ Λ Γ₂ i) (Ξ ++ Γ₂))
                        (split-++ˡ (split-++ʳ Γ₁ s) Γ₂) (split-++ʳ Γ₁ (split-++ˡ s Γ₂))
split-++ˡʳ-comm []       s Γ₂ = refl
split-++ˡʳ-comm (a ∷ Γ₁) s Γ₂ i = there (split-++ˡʳ-comm Γ₁ s Γ₂ i)

-- ==========================================================================
-- The weakenings act on the canonical split as expected.
-- ==========================================================================

split-here-++ˡ : ∀ (Θ : Ctx) (x : Ty) (Ξ Γ₂ : Ctx)
               → PathP (λ i → Split x Θ (++-assoc Θ (x ∷ Ξ) Γ₂ i) (Ξ ++ Γ₂))
                       (split-++ˡ (split-here Θ x Ξ) Γ₂) (split-here Θ x (Ξ ++ Γ₂))
split-here-++ˡ []      x Ξ Γ₂ = refl
split-here-++ˡ (a ∷ Θ) x Ξ Γ₂ i = there (split-here-++ˡ Θ x Ξ Γ₂ i)

split-here-++ʳ : ∀ (Γ₁ Θ : Ctx) (x : Ty) (Ξ : Ctx)
               → PathP (λ i → Split x (Γ₁ ++ Θ) (++-assoc Γ₁ Θ (x ∷ Ξ) (~ i)) Ξ)
                       (split-++ʳ Γ₁ (split-here Θ x Ξ)) (split-here (Γ₁ ++ Θ) x Ξ)
split-here-++ʳ []       Θ x Ξ = refl
split-here-++ʳ (a ∷ Γ₁) Θ x Ξ i = there (split-here-++ʳ Γ₁ Θ x Ξ i)

-- ==========================================================================
-- split-path on the canonical split and on the weakenings.
-- ==========================================================================

split-path-here : ∀ (Θ : Ctx) (x : Ty) (Ξ : Ctx)
                → split-path (split-here Θ x Ξ) ≡ refl
split-path-here []      x Ξ = refl
split-path-here (a ∷ Θ) x Ξ = ap (ap (a ∷_)) (split-path-here Θ x Ξ)

-- Every split is the canonical one, over its own witnessed path.  This is
-- the "to-path-over" of an identity system: Split x Θ – Ξ is the graph of
-- split-here (its total space Σ Ρ (Split x Θ Ρ Ξ) is contractible, with no
-- set-ness of Ty — split-canon paired with split-path IS the contraction),
-- so Split x Θ Ρ Ξ ≃ (Θ ++ x ∷ Ξ ≡ Ρ) and a PathP between splits carries
-- exactly the information of a square between their split-paths.  The
-- cons-by-cons split squares in this development (co-* and friends) are the
-- optimal concrete form of those squares — each mirrors its boundary path's
-- own recursion — which is why none of them route through this fact.
split-canon : (s : Split x Θ Λ Ξ)
            → PathP (λ i → Split x Θ (split-path s i) Ξ) (split-here Θ x Ξ) s
split-canon here        = refl
split-canon (there s) i = there (split-canon s i)

-- Squares relating split-path before/after weakening; the moving edge is
-- ++-assoc, the still edge is the weakened carrier.
split-path-++ˡ : (s : Split x Θ Λ Ξ) (Γ₂ : Ctx)
               → PathP (λ i → ++-assoc Θ (x ∷ Ξ) Γ₂ i ≡ Λ ++ Γ₂)
                       (ap (_++ Γ₂) (split-path s)) (split-path (split-++ˡ s Γ₂))
split-path-++ˡ here              Γ₂ = refl
split-path-++ˡ (there {a = a} s) Γ₂ i j = a ∷ split-path-++ˡ s Γ₂ i j

split-path-++ʳ : (Γ₁ : Ctx) (s : Split x Θ Λ Ξ)
               → PathP (λ i → ++-assoc Γ₁ Θ (x ∷ Ξ) i ≡ Γ₁ ++ Λ)
                       (split-path (split-++ʳ Γ₁ s)) (ap (Γ₁ ++_) (split-path s))
split-path-++ʳ []       s = refl
split-path-++ʳ (a ∷ Γ₁) s i j = a ∷ split-path-++ʳ Γ₁ s i j

-- ==========================================================================
-- split-path on split-behind.  The witnessed path of split-behind s₁ s₂ is,
-- morally, "reassociate, rewrite inside along split-path s₂, then follow
-- split-path s₁" — but stating that with ∙ would violate the structural
-- discipline.  Instead: split-behind-base fuses the reassociation and the
-- inner rewrite into one cons-by-cons path, split-behind-base-assoc
-- characterises it as a square over ++-assoc (so downstream users can
-- reconcile with any ∙-phrased boundary without this file ever forming one),
-- and split-behind-path is the square whose still edges are the two
-- split-paths and whose moving edge is split-behind-base.
-- ==========================================================================

-- (Θ ++ x ∷ Μ) ++ y ∷ Κ ≡ Θ ++ x ∷ Ξ, structurally, given p : Μ ++ y ∷ Κ ≡ Ξ.
split-behind-base : ∀ (Θ : Ctx) (x : Ty) {y : Ty} {Μ Κ Ξ : Ctx}
                  → Μ ++ y ∷ Κ ≡ Ξ
                  → (Θ ++ x ∷ Μ) ++ y ∷ Κ ≡ Θ ++ x ∷ Ξ
split-behind-base []      x p i = x ∷ p i
split-behind-base (a ∷ Θ) x p i = a ∷ split-behind-base Θ x p i

-- Characterisation: over ++-assoc, split-behind-base is ap of the inner path.
split-behind-base-assoc : ∀ (Θ : Ctx) (x : Ty) {y : Ty} {Μ Κ Ξ : Ctx}
                          (p : Μ ++ y ∷ Κ ≡ Ξ)
                        → PathP (λ i → ++-assoc Θ (x ∷ Μ) (y ∷ Κ) i ≡ Θ ++ x ∷ Ξ)
                                (split-behind-base Θ x p)
                                (ap (λ Ξ' → Θ ++ x ∷ Ξ') p)
split-behind-base-assoc []      x p = refl
split-behind-base-assoc (a ∷ Θ) x p i j = a ∷ split-behind-base-assoc Θ x p i j

split-behind-path : (s₁ : Split x Θ Ρ Ξ) (s₂ : Split y Μ Ξ Κ)
                  → PathP (λ i → split-behind-base Θ x (split-path s₂) i ≡ Ρ)
                          (split-path (split-behind s₁ s₂)) (split-path s₁)
split-behind-path {x = x} here      s₂ i j = x ∷ split-path s₂ (i ∨ j)
split-behind-path (there {a = a} s₁) s₂ i j = a ∷ split-behind-path s₁ s₂ i j
