open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
open import Multicategory.Free

module Multicategory.Free.Interchange {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G
open import ListPath.Solver using (list!)

-- Interchange of substitution (Shulman, Lemma 2.4.9, interchange half):
-- plugging g and h into two disjoint slots of the same term commutes, over
-- the structural boundary interchangeₘ-boundary.  The slot data: s₁ marks x
-- in t's context Ρ, and s₂ marks y inside s₁'s suffix Ξ, so y sits strictly
-- behind x.  On the left h is plugged after g (into the surviving y-slot
-- split-++ʳ Θ (split-++ʳ Γ s₂)); on the right h goes first (into
-- split-behind s₁ s₂) and g afterwards (into the canonical surviving x-slot).
--
-- Proof architecture:
--   §1  fusion laws for split-behind against the canonical weakenings
--   §2  Split²-++, the two-slot analogue of Split-++: a view with soundness
--       locating BOTH slots relative to a decomposition Γ₁ ++ Δ₁ of the
--       carrier, computed by the same refl-or-cons recursion as split-++
--   §3  cons-step helpers for the base-path squares, and small path algebra
--   §4  split-square (co-) lemmas: PathP's of splits over the flatten paths
--   §5  the base-path squares (composite of structural paths ≡ structural)
--   §6  canonicalisers: transport a goal stated at the canonical splits to
--       one stated at abstract splits, along the soundness fields of §2
--   §7  the mutual induction, one core lemma per (constructor × slot-case)

private module G = Multigraph G

private variable
  As : List G.Ob

-- ==========================================================================
-- §1  split-behind fusion
-- ==========================================================================

-- Both slots weakened by a common suffix: split-behind fuses homogeneously.
split-behind-++ˡ
  : ∀ {x y : Ty} {Θ Λ Ξ₁ Μ Κ₁ : Ctx}
    (s₁ : Split x Θ Λ Ξ₁) (s₂ : Split y Μ Ξ₁ Κ₁) (Δ₁ : Ctx)
  → split-behind (split-++ˡ s₁ Δ₁) (split-++ˡ s₂ Δ₁)
  ≡ split-++ˡ (split-behind s₁ s₂) Δ₁
split-behind-++ˡ here       s₂ Δ₁ = refl
split-behind-++ˡ (there s₁) s₂ Δ₁ = ap there (split-behind-++ˡ s₁ s₂ Δ₁)

-- Both slots buried under a common prefix: split-behind fuses over ++-assoc.
split-behind-++ʳ
  : ∀ {x y : Ty} {Θ Λ Ξ Μ Κ : Ctx}
    (Γ₁ : Ctx) (s₁ : Split x Θ Λ Ξ) (s₂ : Split y Μ Ξ Κ)
  → PathP (λ i → Split y (++-assoc Γ₁ Θ (x ∷ Μ) i) (Γ₁ ++ Λ) Κ)
      (split-behind (split-++ʳ Γ₁ s₁) s₂)
      (split-++ʳ Γ₁ (split-behind s₁ s₂))
split-behind-++ʳ []       s₁ s₂ = refl
split-behind-++ʳ (a ∷ Γ₁) s₁ s₂ i = there (split-behind-++ʳ Γ₁ s₁ s₂ i)

-- The cross case: x in the carrier of s₁, y in a disjoint region Δ₁ appended
-- after it.  The prefix of the fused slot reassociates along this structural
-- path (cons-by-cons over s₁; the base case is definitional).
behind-cross-base
  : ∀ {x : Ty} {Θ Ξ₁ : Ctx} {Λ : Ctx}
  → Split x Θ Λ Ξ₁ → (Μ₂ : Ctx) → Λ ++ Μ₂ ≡ Θ ++ x ∷ (Ξ₁ ++ Μ₂)
behind-cross-base here              Μ₂ = refl
behind-cross-base (there {a = a} s) Μ₂ = ap (a ∷_) (behind-cross-base s Μ₂)

split-behind-cross
  : ∀ {x y : Ty} {Θ Λ Ξ₁ Μ₂ Δ₁ Κ : Ctx}
    (s₁ : Split x Θ Λ Ξ₁) (s₂ : Split y Μ₂ Δ₁ Κ)
  → PathP (λ i → Split y (behind-cross-base s₁ Μ₂ i) (Λ ++ Δ₁) Κ)
      (split-++ʳ Λ s₂)
      (split-behind (split-++ˡ s₁ Δ₁) (split-++ʳ Ξ₁ s₂))
split-behind-cross here       s₂ = refl
split-behind-cross (there s₁) s₂ i = there (split-behind-cross s₁ s₂ i)

-- ==========================================================================
-- §2  The two-slot view
-- ==========================================================================

-- Split²-++ Γ₁ Δ₁ s₁ s₂ locates the ordered pair of slots (x via s₁, y via
-- s₂ inside s₁'s suffix) relative to the decomposition Γ₁ ++ Δ₁ of s₁'s
-- carrier.  Three cases are possible (y cannot sit left of x); each carries
-- the canonical component splits, the boundary paths, and PathP soundness
-- fields reconstituting s₁ and s₂ from them — exactly what the transport in
-- §6 consumes.  Computed by the same refl-or-cons recursion as split-++:
-- the s₂-analysis happens at the moment s₁'s view bottoms out at `here`,
-- when the suffix Ξ is *definitionally* Ξ₁ ++ Δ₁.
data Split²-++ (Γ₁ Δ₁ : Ctx) {x y : Ty} {Θ Μ Ξ Κ : Ctx}
               (s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ) (s₂ : Split y Μ Ξ Κ) : Type o where
  both-left
    : ∀ {Ξ₁ Κ₁ : Ctx} (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
        (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΚ : Κ₁ ++ Δ₁ ≡ Κ)
    → PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁
    → PathP (λ i → Split y Μ (pΞ i) (pΚ i)) (split-++ˡ s₂' Δ₁) s₂
    → Split²-++ Γ₁ Δ₁ s₁ s₂
  cross
    : ∀ {Ξ₁ Μ₂ : Ctx} (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ₂ Δ₁ Κ)
        (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΜ : Ξ₁ ++ Μ₂ ≡ Μ)
    → PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁
    → PathP (λ i → Split y (pΜ i) (pΞ i) Κ) (split-++ʳ Ξ₁ s₂') s₂
    → Split²-++ Γ₁ Δ₁ s₁ s₂
  both-right
    : ∀ {Θ₂ : Ctx} (s₁' : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    → PathP (λ i → Split x (q i) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₁') s₁
    → Split²-++ Γ₁ Δ₁ s₁ s₂

-- The cons step, as a named function (proofs about view² are then plain aps).
view²-step
  : ∀ {Γ₁ Δ₁ : Ctx} {a x y : Ty} {Θ Μ Ξ Κ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Γ₁ Δ₁ s₁ s₂ → Split²-++ (a ∷ Γ₁) Δ₁ (there s₁) s₂
view²-step (both-left s₁' s₂' pΞ pΚ c₁ c₂) =
  both-left (there s₁') s₂' pΞ pΚ (λ i → there (c₁ i)) c₂
view²-step (cross s₁' s₂' pΞ pΜ c₁ c₂) =
  cross (there s₁') s₂' pΞ pΜ (λ i → there (c₁ i)) c₂
view²-step (both-right s₁' q c₁) =
  both-right s₁' (ap (_ ∷_) q) (λ i → there (c₁ i))

-- The `here` step: the suffix is now literally Γ₁ ++ Δ₁, so the location of
-- y is read off from the ordinary view of s₂.
view²-here
  : ∀ {Γ₁ Δ₁ : Ctx} {x y : Ty} {Μ Κ : Ctx} {s₂ : Split y Μ (Γ₁ ++ Δ₁) Κ}
  → Split-++ Γ₁ Δ₁ s₂
  → Split²-++ (x ∷ Γ₁) Δ₁ (here {Ξ = Γ₁ ++ Δ₁}) s₂
view²-here (on-left  s₂' p co) = both-left here s₂' refl p refl co
view²-here (on-right s₂' q co) = cross here s₂' refl q refl co

view² : ∀ (Γ₁ : Ctx) {Δ₁ : Ctx} {x y : Ty} {Θ Μ Ξ Κ : Ctx}
        (s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ) (s₂ : Split y Μ Ξ Κ)
      → Split²-++ Γ₁ Δ₁ s₁ s₂
view² []       s₁         s₂ = both-right s₁ refl refl
view² (a ∷ Γ₁) here       s₂ = view²-here (split-++ Γ₁ s₂)
view² (a ∷ Γ₁) (there s₁) s₂ = view²-step (view² Γ₁ s₁ s₂)

-- flattenʳ is the inverse reassociation, named.
flattenʳ≡ : ∀ (Γ₁ Θ₂ Γ Ξ : Ctx)
          → flattenʳ Γ₁ Θ₂ Γ Ξ ≡ sym (++-assoc Γ₁ Θ₂ (Γ ++ Ξ))
flattenʳ≡ Γ₁ Θ₂ Γ Ξ = list!

-- (cast-∙idr / sp-cast-∙idr, collapsing the ∙ refl left by the p-component
-- of a view computation, come from Kit.)

-- ==========================================================================
-- §4  Split squares: PathP's of splits over the flatten paths.  All are
-- cons-by-cons; the bases delegate to the SplitLemmas coherences.
-- ==========================================================================

-- Weakening the y-slot by a suffix Δ₁ commutes with burying it under Θ, Γ,
-- over flattenˡ.  (Peels the left side's outer cast in the *-LL cores.)
co-ʳʳˡ : ∀ (Θ Γ : Ctx) {y : Ty} {Μ Ξ₁ Κ₁ : Ctx}
         (s : Split y Μ Ξ₁ Κ₁) (Δ₁ : Ctx)
       → PathP (λ i → Split y (Θ ++ Γ ++ Μ) (flattenˡ Θ Γ Ξ₁ Δ₁ i) (Κ₁ ++ Δ₁))
           (split-++ˡ (split-++ʳ Θ (split-++ʳ Γ s)) Δ₁)
           (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s Δ₁)))
co-ʳʳˡ []      Γ s Δ₁ = split-++ˡʳ-comm Γ s Δ₁
co-ʳʳˡ (a ∷ Θ) Γ s Δ₁ i = there (co-ʳʳˡ Θ Γ s Δ₁ i)

-- The canonical x-slot absorbs a suffix weakening, over flattenˡ (both in
-- the carrier and in the suffix).  (Peels the right side's outer cast in
-- the *-LL cores.)
co-hereˡ : ∀ (Θ : Ctx) (x : Ty) (Μ Δ' Κ₁ Δ₁ : Ctx)
         → PathP (λ i → Split x Θ (flattenˡ (Θ ++ x ∷ Μ) Δ' Κ₁ Δ₁ i)
                                  (flattenˡ Μ Δ' Κ₁ Δ₁ i))
             (split-++ˡ (split-++ˡ (split-here Θ x Μ) (Δ' ++ Κ₁)) Δ₁)
             (split-++ˡ (split-here Θ x Μ) (Δ' ++ Κ₁ ++ Δ₁))
co-hereˡ []      x Μ Δ' Κ₁ Δ₁ i = here {Ξ = flattenˡ Μ Δ' Κ₁ Δ₁ i}
co-hereˡ (a ∷ Θ) x Μ Δ' Κ₁ Δ₁ i = there (co-hereˡ Θ x Μ Δ' Κ₁ Δ₁ i)

-- Prefix burials reassociate, over flattenʳ.  (Peels the left side's outer
-- cast in the *-RR cores.)
co-ʳʳʳ : ∀ (Γ₁ Θ₂ Γ : Ctx) {y : Ty} {Μ Ξ Κ : Ctx} (s : Split y Μ Ξ Κ)
       → PathP (λ i → Split y (flattenʳ Γ₁ Θ₂ Γ Μ i) (flattenʳ Γ₁ Θ₂ Γ Ξ i) Κ)
           (split-++ʳ Γ₁ (split-++ʳ Θ₂ (split-++ʳ Γ s)))
           (split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s))
co-ʳʳʳ []       Θ₂ Γ s = refl
co-ʳʳʳ (a ∷ Γ₁) Θ₂ Γ s i = there (co-ʳʳʳ Γ₁ Θ₂ Γ s i)

-- The buried canonical x-slot commutes with suffix weakening, over
-- flattenʳ.  (Peels the right side's outer cast in the *-RR cores.)
co-hereʳ : ∀ (Γ₁ Θ₂ : Ctx) (x : Ty) (Μ Δ' Κ : Ctx)
         → PathP (λ i → Split x (Γ₁ ++ Θ₂) (flattenʳ Γ₁ (Θ₂ ++ x ∷ Μ) Δ' Κ i)
                                (Μ ++ Δ' ++ Κ))
             (split-++ʳ Γ₁ (split-++ˡ (split-here Θ₂ x Μ) (Δ' ++ Κ)))
             (split-++ˡ (split-++ʳ Γ₁ (split-here Θ₂ x Μ)) (Δ' ++ Κ))
co-hereʳ []       Θ₂ x Μ Δ' Κ = refl
co-hereʳ (a ∷ Γ₁) Θ₂ x Μ Δ' Κ i = there (co-hereʳ Γ₁ Θ₂ x Μ Δ' Κ i)

-- Burying the disjoint y-slot under Θ, Γ and the first slot's suffix Ξ₁,
-- over flattenˡ.  (Peels the left side's outer cast in the cross cores.)
co-crossˡ : ∀ (Θ Γ Ξ₁ : Ctx) {y : Ty} {Μ₂ Δ₁ Κ : Ctx} (s : Split y Μ₂ Δ₁ Κ)
          → PathP (λ i → Split y (flattenˡ Θ Γ Ξ₁ Μ₂ i) (flattenˡ Θ Γ Ξ₁ Δ₁ i) Κ)
              (split-++ʳ (Θ ++ Γ ++ Ξ₁) s)
              (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s)))
co-crossˡ []      Γ Ξ₁ s = split-++ʳ-++ Γ Ξ₁ s
co-crossˡ (a ∷ Θ) Γ Ξ₁ s i = there (co-crossˡ Θ Γ Ξ₁ s i)

-- Suffix weakenings of the x-slot reassociate, over flattenʳ (carrier and
-- suffix).  (Peels the right side's outer cast in the cross cores.)
co-crossʳ : ∀ {x : Ty} {Θ Γ₁ Ξ₁ : Ctx}
            (s₁ : Split x Θ Γ₁ Ξ₁) (Μ₂ Δ' Κ : Ctx)
          → PathP (λ i → Split x Θ (flattenʳ Γ₁ Μ₂ Δ' Κ i) (flattenʳ Ξ₁ Μ₂ Δ' Κ i))
              (split-++ˡ s₁ (Μ₂ ++ Δ' ++ Κ))
              (split-++ˡ (split-++ˡ s₁ Μ₂) (Δ' ++ Κ))
co-crossʳ {Ξ₁ = Ξ₁} here Μ₂ Δ' Κ i = here {Ξ = flattenʳ Ξ₁ Μ₂ Δ' Κ i}
co-crossʳ (there s₁) Μ₂ Δ' Κ i = there (co-crossʳ s₁ Μ₂ Δ' Κ i)

-- The canonical x-slot of the cross cores' right side: after h lands in the
-- disjoint region, the slot x is still the canonical one, over
-- behind-cross-base weakened by the tail.
co-crossʰ : ∀ {x : Ty} {Θ Γ₁ Ξ₁ : Ctx}
            (s₁ : Split x Θ Γ₁ Ξ₁) (Μ₂ Φ : Ctx)
          → PathP (λ j → Split x Θ (behind-cross-base s₁ Μ₂ j ++ Φ) ((Ξ₁ ++ Μ₂) ++ Φ))
              (split-++ˡ (split-++ˡ s₁ Μ₂) Φ)
              (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) Φ)
co-crossʰ here        Μ₂ Φ = refl
co-crossʰ (there s₁)  Μ₂ Φ j = there (co-crossʰ s₁ Μ₂ Φ j)

-- Middle-region variants for the match ʳ-handlers: the y-slot buried in the
-- weakened Ψ-region, over flattenᵐ.
co-mid : ∀ (Γm Θ₂ Γ : Ctx) {y : Ty} {Μ Ξ₁ Κ₁ : Ctx}
         (s : Split y Μ Ξ₁ Κ₁) (Δm : Ctx)
       → PathP (λ i → Split y (flattenʳ Γm Θ₂ Γ Μ i) (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm i)
                              (Κ₁ ++ Δm))
           (split-++ʳ Γm (split-++ˡ (split-++ʳ Θ₂ (split-++ʳ Γ s)) Δm))
           (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ˡ s Δm)))
co-mid []       Θ₂ Γ s Δm = co-ʳʳˡ Θ₂ Γ s Δm
co-mid (a ∷ Γm) Θ₂ Γ s Δm i = there (co-mid Γm Θ₂ Γ s Δm i)

-- The buried canonical x-slot of the middle region absorbs the trailing
-- weakening, over flattenᵐ (carrier) and flattenˡ (suffix).
co-midʰ : ∀ (Γm Θ₂ : Ctx) (x : Ty) (Μ Δ' Κ₁ Δm : Ctx)
        → PathP (λ i → Split x (Γm ++ Θ₂) (flattenᵐ Γm (Θ₂ ++ x ∷ Μ) Δ' Κ₁ Δm i)
                               (flattenˡ Μ Δ' Κ₁ Δm i))
            (split-++ʳ Γm (split-++ˡ (split-++ˡ (split-here Θ₂ x Μ) (Δ' ++ Κ₁)) Δm))
            (split-++ˡ (split-++ʳ Γm (split-here Θ₂ x Μ)) (Δ' ++ Κ₁ ++ Δm))
co-midʰ []       Θ₂ x Μ Δ' Κ₁ Δm = co-hereˡ Θ₂ x Μ Δ' Κ₁ Δm
co-midʰ (a ∷ Γm) Θ₂ x Μ Δ' Κ₁ Δm i = there (co-midʰ Γm Θ₂ x Μ Δ' Κ₁ Δm i)

-- Four-deep prefix burial reassociates, over bury.  (Peels the left casts
-- of the ΔΔ cores.)
co-bury : ∀ (Γm Ψ Θ₃ Γ : Ctx) {y : Ty} {Μ Ξ Κ : Ctx} (s : Split y Μ Ξ Κ)
        → PathP (λ i → Split y (bury Γm Ψ Θ₃ (Γ ++ Μ) i) (bury Γm Ψ Θ₃ (Γ ++ Ξ) i) Κ)
            (split-++ʳ Γm (split-++ʳ Ψ (split-++ʳ Θ₃ (split-++ʳ Γ s))))
            (split-++ʳ (Γm ++ Ψ ++ Θ₃) (split-++ʳ Γ s))
co-bury []       Ψ Θ₃ Γ s = symP (split-++ʳ-++ Ψ Θ₃ (split-++ʳ Γ s))
co-bury (a ∷ Γm) Ψ Θ₃ Γ s i = there (co-bury Γm Ψ Θ₃ Γ s i)

-- The buried canonical x-slot of the last region commutes with the suffix
-- weakening, over bury.  (Peels the right casts of the ΔΔ cores.)
co-buryʰ : ∀ (Γm Ψ Θ₃ : Ctx) (x : Ty) (Μ Φ : Ctx)
         → PathP (λ i → Split x (Γm ++ Ψ ++ Θ₃) (bury Γm Ψ (Θ₃ ++ x ∷ Μ) Φ i)
                                (Μ ++ Φ))
             (split-++ʳ Γm (split-++ʳ Ψ (split-++ˡ (split-here Θ₃ x Μ) Φ)))
             (split-++ˡ (split-++ʳ Γm (split-++ʳ Ψ (split-here Θ₃ x Μ))) Φ)
co-buryʰ []       Ψ Θ₃ x Μ Φ = symP (split-++ˡʳ-comm Ψ (split-here Θ₃ x Μ) Φ)
co-buryʰ (a ∷ Γm) Ψ Θ₃ x Μ Φ i = there (co-buryʰ Γm Ψ Θ₃ x Μ Φ i)

-- Prefix burial commutes with suffix weakening, over flattenʳ.  (The
-- generalisation of co-hereʳ used by the inner layer of the ΔΔ cores.)
co-flʳˡ : ∀ (Γ₁ : Ctx) {x : Ty} {Θ' Λ Ξ' : Ctx} (s : Split x Θ' Λ Ξ') (Δ' Κ' : Ctx)
        → PathP (λ i → Split x (Γ₁ ++ Θ') (flattenʳ Γ₁ Λ Δ' Κ' i) (Ξ' ++ Δ' ++ Κ'))
            (split-++ʳ Γ₁ (split-++ˡ s (Δ' ++ Κ')))
            (split-++ˡ (split-++ʳ Γ₁ s) (Δ' ++ Κ'))
co-flʳˡ []       s Δ' Κ' = refl
co-flʳˡ (a ∷ Γ₁) s Δ' Κ' i = there (co-flʳˡ Γ₁ s Δ' Κ' i)

-- The first slot's canonical position under a cross fusion, without the
-- appended tail (primitive of co-crossʰ).
co-crossᵖ : ∀ {x : Ty} {Θ Λ Ξ₁ : Ctx} (s₁ : Split x Θ Λ Ξ₁) (Μ₂ : Ctx)
          → PathP (λ j → Split x Θ (behind-cross-base s₁ Μ₂ j) (Ξ₁ ++ Μ₂))
              (split-++ˡ s₁ Μ₂) (split-here Θ x (Ξ₁ ++ Μ₂))
co-crossᵖ here       Μ₂ = refl
co-crossᵖ (there s₁) Μ₂ j = there (co-crossᵖ s₁ Μ₂ j)

-- Suffix weakenings reassociate over flattenᵐ (both carriers).  (Peels the
-- right cast of the ΓΨ cores.)
co-crossᵐ : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁)
            (Μ₂ Δ' Κᵧ Δm : Ctx)
          → PathP (λ i → Split x Θ (flattenᵐ Γm Μ₂ Δ' Κᵧ Δm i)
                                   (flattenᵐ Ξ₁ Μ₂ Δ' Κᵧ Δm i))
              (split-++ˡ s₁ ((Μ₂ ++ Δ' ++ Κᵧ) ++ Δm))
              (split-++ˡ (split-++ˡ s₁ Μ₂) (Δ' ++ Κᵧ ++ Δm))
co-crossᵐ {Ξ₁ = Ξ₁} here Μ₂ Δ' Κᵧ Δm i = here {Ξ = flattenᵐ Ξ₁ Μ₂ Δ' Κᵧ Δm i}
co-crossᵐ (there s₁) Μ₂ Δ' Κᵧ Δm i = there (co-crossᵐ s₁ Μ₂ Δ' Κᵧ Δm i)

-- Suffix weakenings reassociate over bury (both carriers).  (Peels the
-- right cast of the ΓΔ cores.)
co-crossᵇ : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (Ψ Μᵧ Φ : Ctx)
          → PathP (λ i → Split x Θ (bury Γm Ψ Μᵧ Φ i) (bury Ξ₁ Ψ Μᵧ Φ i))
              (split-++ˡ s₁ (Ψ ++ Μᵧ ++ Φ))
              (split-++ˡ (split-++ˡ s₁ (Ψ ++ Μᵧ)) Φ)
co-crossᵇ {Ξ₁ = Ξ₁} here Ψ Μᵧ Φ i = here {Ξ = bury Ξ₁ Ψ Μᵧ Φ i}
co-crossᵇ (there s₁) Ψ Μᵧ Φ i = there (co-crossᵇ s₁ Ψ Μᵧ Φ i)

-- The y-slot of the last region under the middle-region weakenings, over
-- flattenᵐ.  (Peels the left cast of the ΨΔ cores.)
co-midᵧ : ∀ (Γm Θ₂ Γ Ξ₁ : Ctx) {y : Ty} {Μᵧ Δm Κ : Ctx} (s : Split y Μᵧ Δm Κ)
        → PathP (λ i → Split y (flattenᵐ Γm Θ₂ Γ Ξ₁ Μᵧ i)
                               (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm i) Κ)
            (split-++ʳ Γm (split-++ʳ (Θ₂ ++ Γ ++ Ξ₁) s))
            (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ʳ Ξ₁ s)))
co-midᵧ []       Θ₂ Γ Ξ₁ s = co-crossˡ Θ₂ Γ Ξ₁ s
co-midᵧ (a ∷ Γm) Θ₂ Γ Ξ₁ s i = there (co-midᵧ Γm Θ₂ Γ Ξ₁ s i)

-- The buried middle-region x-slot commutes with the trailing weakening,
-- over bury.  (Peels the right cast of the ΨΔ cores.)
co-midᵇ : ∀ (Γm : Ctx) {x : Ty} {Θ₂ Ψ Ξ₁ : Ctx} (s₁ : Split x Θ₂ Ψ Ξ₁)
          (Μᵧ Δ' Κ' : Ctx)
        → PathP (λ i → Split x (Γm ++ Θ₂) (bury Γm Ψ Μᵧ (Δ' ++ Κ') i)
                               (flattenʳ Ξ₁ Μᵧ Δ' Κ' i))
            (split-++ʳ Γm (split-++ˡ s₁ (Μᵧ ++ Δ' ++ Κ')))
            (split-++ˡ (split-++ʳ Γm (split-++ˡ s₁ Μᵧ)) (Δ' ++ Κ'))
co-midᵇ [] {Ψ = Ψ} s₁ Μᵧ Δ' Κ' =
  split-over refl refl (flattenʳ≡ Ψ Μᵧ Δ' Κ') (co-crossʳ s₁ Μᵧ Δ' Κ')
co-midᵇ (a ∷ Γm) s₁ Μᵧ Δ' Κ' i = there (co-midᵇ Γm s₁ Μᵧ Δ' Κ' i)

-- ==========================================================================
-- §5  Base-path squares, discharged by the generic list-path solver: each
-- reconciles a composite of structural reassociations against the target
-- interchange boundary, which is exactly the solver's decision problem
-- (ListPath.Solver's list! macro).
-- ==========================================================================

sq-LL : ∀ (Θ Γ Μ Δ Κ₁ Δ₁ : Ctx)
  → ((sym (flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ Δ₁)
      ∙ ap (_++ Δ₁) (interchangeₘ-boundary Θ Γ Μ Δ Κ₁))
     ∙ flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) Δ₁)
    ∙ ap (λ l → Θ ++ Γ ++ l) (flattenˡ Μ Δ Κ₁ Δ₁)
  ≡ interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁)
sq-LL Θ Γ Μ Δ Κ₁ Δ₁ = list!

sq-RR : ∀ (Γ₁ Θ₂ Γ Μ Δ Κ : Ctx)
  → ((sym (ap (_++ Δ ++ Κ) (flattenʳ Γ₁ Θ₂ Γ Μ))
      ∙ sym (flattenʳ Γ₁ (Θ₂ ++ Γ ++ Μ) Δ Κ))
     ∙ ap (Γ₁ ++_) (interchangeₘ-boundary Θ₂ Γ Μ Δ Κ))
    ∙ flattenʳ Γ₁ Θ₂ Γ (Μ ++ Δ ++ Κ)
  ≡ interchangeₘ-boundary (Γ₁ ++ Θ₂) Γ Μ Δ Κ
sq-RR Γ₁ Θ₂ Γ Μ Δ Κ = list!

sq-LR : ∀ (Θ Γ Ξ₁ Μ₂ Δ Κ : Ctx)
  → ((sym (ap (_++ Δ ++ Κ) (flattenˡ Θ Γ Ξ₁ Μ₂))
      ∙ sym (flattenʳ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κ))
     ∙ flattenˡ Θ Γ Ξ₁ (Μ₂ ++ Δ ++ Κ))
    ∙ ap (λ l → Θ ++ Γ ++ l) (flattenʳ Ξ₁ Μ₂ Δ Κ)
  ≡ interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ
sq-LR Θ Γ Ξ₁ Μ₂ Δ Κ = list!

sq-LL-inv : ∀ (Θ Γ Μ Δ Κ₁ Δ₁ : Ctx)
  → ((flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ Δ₁ ∙ interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁))
     ∙ ap (λ l → Θ ++ Γ ++ l) (sym (flattenˡ Μ Δ Κ₁ Δ₁)))
    ∙ sym (flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) Δ₁)
  ≡ ap (_++ Δ₁) (interchangeₘ-boundary Θ Γ Μ Δ Κ₁)
sq-LL-inv Θ Γ Μ Δ Κ₁ Δ₁ = list!

sq-ΨΨ : ∀ (Γm Θ₂ Γ Μ Δ Κ₁ Δm : Ctx)
  → (((sym (ap (_++ Δ ++ Κ₁ ++ Δm) (flattenʳ Γm Θ₂ Γ Μ))
        ∙ sym (flattenᵐ Γm (Θ₂ ++ Γ ++ Μ) Δ Κ₁ Δm))
       ∙ ap (λ l → Γm ++ l ++ Δm) (interchangeₘ-boundary Θ₂ Γ Μ Δ Κ₁))
      ∙ flattenᵐ Γm Θ₂ Γ (Μ ++ Δ ++ Κ₁) Δm)
     ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) (flattenˡ Μ Δ Κ₁ Δm)
  ≡ interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ (Κ₁ ++ Δm)
sq-ΨΨ Γm Θ₂ Γ Μ Δ Κ₁ Δm = list!

sq-ΔΔ-outer : ∀ (Γm Ψ Θ₃ Γ Μ Δ Κ : Ctx)
  → ((sym (ap (_++ Δ ++ Κ) (bury Γm Ψ Θ₃ (Γ ++ Μ)))
       ∙ sym (bury Γm Ψ (Θ₃ ++ Γ ++ Μ) (Δ ++ Κ)))
      ∙ ap (λ l → Γm ++ Ψ ++ l) (interchangeₘ-boundary Θ₃ Γ Μ Δ Κ))
     ∙ bury Γm Ψ Θ₃ (Γ ++ Μ ++ Δ ++ Κ)
  ≡ interchangeₘ-boundary (Γm ++ Ψ ++ Θ₃) Γ Μ Δ Κ
sq-ΔΔ-outer Γm Ψ Θ₃ Γ Μ Δ Κ = list!

sq-ΓΨ : ∀ (Θ Γ Ξ₁ Μ₂ Δ Κᵧ Δm : Ctx)
  → ((sym (ap (_++ Δ ++ Κᵧ ++ Δm) (flattenˡ Θ Γ Ξ₁ Μ₂))
      ∙ sym (flattenᵐ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κᵧ Δm))
     ∙ flattenˡ Θ Γ Ξ₁ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm))
    ∙ ap (λ l → Θ ++ Γ ++ l) (flattenᵐ Ξ₁ Μ₂ Δ Κᵧ Δm)
  ≡ interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ (Κᵧ ++ Δm)
sq-ΓΨ Θ Γ Ξ₁ Μ₂ Δ Κᵧ Δm = list!

sq-ΨΔ : ∀ (Γm Θ₂ Γ Ξ₁ Μᵧ Δ Κ : Ctx)
  → ((sym (ap (_++ Δ ++ Κ) (flattenᵐ Γm Θ₂ Γ Ξ₁ Μᵧ))
      ∙ sym (bury Γm (Θ₂ ++ Γ ++ Ξ₁) Μᵧ (Δ ++ Κ)))
     ∙ flattenᵐ Γm Θ₂ Γ Ξ₁ (Μᵧ ++ Δ ++ Κ))
    ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) (flattenʳ Ξ₁ Μᵧ Δ Κ)
  ≡ interchangeₘ-boundary (Γm ++ Θ₂) Γ (Ξ₁ ++ Μᵧ) Δ Κ
sq-ΨΔ Γm Θ₂ Γ Ξ₁ Μᵧ Δ Κ = list!

sq-ΓΔ-inner : ∀ (Θ Γ Ξ₁ Ν Δ Κ : Ctx)
  → (((flattenʳ (Θ ++ Γ ++ Ξ₁) Ν Δ Κ
       ∙ ap (_++ Δ ++ Κ) (flattenˡ Θ Γ Ξ₁ Ν))
      ∙ interchangeₘ-boundary Θ Γ (Ξ₁ ++ Ν) Δ Κ)
     ∙ ap (λ l → Θ ++ Γ ++ l) (sym (flattenʳ Ξ₁ Ν Δ Κ)))
    ∙ sym (flattenˡ Θ Γ Ξ₁ (Ν ++ Δ ++ Κ))
  ≡ refl
sq-ΓΔ-inner Θ Γ Ξ₁ Ν Δ Κ = list!

sq-ΓΔ-outer : ∀ (Θ Γ Ξ₁ Ψ Μᵧ Δ Κ : Ctx)
  → ((sym (ap (_++ Δ ++ Κ) (flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ)))
      ∙ sym (bury (Θ ++ Γ ++ Ξ₁) Ψ Μᵧ (Δ ++ Κ)))
     ∙ flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ ++ Δ ++ Κ))
    ∙ ap (λ l → Θ ++ Γ ++ l) (bury Ξ₁ Ψ Μᵧ (Δ ++ Κ))
  ≡ interchangeₘ-boundary Θ Γ (Ξ₁ ++ Ψ ++ Μᵧ) Δ Κ
sq-ΓΔ-outer Θ Γ Ξ₁ Ψ Μᵧ Δ Κ = list!

-- ==========================================================================
-- §6  Canonicalisers.  Transport an interchange goal stated at the canonical
-- (weakened) splits of a Split²-++ case to the goal at the abstract splits,
-- along the soundness fields — everything applied under the interval j.
-- Generic in the analysed term t (resp. spine ts), so all constructor
-- handlers share them.
-- ==========================================================================

canon-LL
  : ∀ {x y z : Ty} {Θ Γ Μ Δ Ξ Κ Ξ₁ Κ₁ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΚ : Κ₁ ++ Δ₁ ≡ Κ)
    (c₁ : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁)
    (c₂ : PathP (λ i → Split y Μ (pΞ i) (pΚ i)) (split-++ˡ s₂' Δ₁) s₂)
    (t : Tm (Γ₁ ++ Δ₁) z) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁) i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁)))
           (sub (split-++ˡ s₁' Δ₁) t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁))
           (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) t h) g)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) t h) g)
canon-LL {x = x} {z = z} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ}
  s₁' s₂' pΞ pΚ c₁ c₂ t g h core =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ (pΚ j) i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ (c₂ j))) (sub (c₁ j) t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ pΚ j))
           (sub (split-behind (c₁ j) (c₂ j)) t h) g))
    core

canon-LR
  : ∀ {x y z : Ty} {Θ Γ Μ Δ Ξ Κ Ξ₁ Μ₂ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ₂ Δ₁ Κ)
    (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΜ : Ξ₁ ++ Μ₂ ≡ Μ)
    (c₁ : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁)
    (c₂ : PathP (λ i → Split y (pΜ i) (pΞ i) Κ) (split-++ʳ Ξ₁ s₂') s₂)
    (t : Tm (Γ₁ ++ Δ₁) z) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
           (sub (split-++ˡ s₁' Δ₁) t g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) t h) g)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) t h) g)
canon-LR {x = x} {z = z} {Θ = Θ} {Γ = Γ} {Δ = Δ} {Κ = Κ}
  s₁' s₂' pΞ pΜ c₁ c₂ t g h core =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (pΜ j) Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ (c₂ j))) (sub (c₁ j) t g) h)
      (sub (split-++ˡ (split-here Θ x (pΜ j)) (Δ ++ Κ))
           (sub (split-behind (c₁ j) (c₂ j)) t h) g))
    core

canon-RR
  : ∀ {x y z : Ty} {Θ Γ Μ Δ Ξ Κ Θ₂ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    (c₁ : PathP (λ i → Split x (q i) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₁') s₁)
    (t : Tm (Γ₁ ++ Δ₁) z) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γ₁ ++ Θ₂) Γ Μ Δ Κ i) z)
      (sub (split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γ₁ s₁') t g) h)
      (sub (split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γ₁ s₁') s₂) t h) g)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) t h) g)
canon-RR {x = x} {z = z} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Κ = Κ} {s₂ = s₂}
  s₁' q c₁ t g h core =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (q j) Γ Μ Δ Κ i) z)
      (sub (split-++ʳ (q j) (split-++ʳ Γ s₂)) (sub (c₁ j) t g) h)
      (sub (split-++ˡ (split-here (q j) x Μ) (Δ ++ Κ))
           (sub (split-behind (c₁ j) s₂) t h) g))
    core

-- Spine versions (identical transports at Sp).

canon-LL-sp
  : ∀ {x y : Ty} {As : List G.Ob} {Θ Γ Μ Δ Ξ Κ Ξ₁ Κ₁ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΚ : Κ₁ ++ Δ₁ ≡ Κ)
    (c₁ : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁)
    (c₂ : PathP (λ i → Split y Μ (pΞ i) (pΚ i)) (split-++ˡ s₂' Δ₁) s₂)
    (ts : Sp (Γ₁ ++ Δ₁) As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁) i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁)))
              (sub-sp (split-++ˡ s₁' Δ₁) ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁))
              (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) ts h) g)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub-sp s₁ ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
              (sub-sp (split-behind s₁ s₂) ts h) g)
canon-LL-sp {x = x} {As = As} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ}
  s₁' s₂' pΞ pΚ c₁ c₂ ts g h core =
  transport
    (λ j → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ (pΚ j) i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (c₂ j))) (sub-sp (c₁ j) ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ pΚ j))
              (sub-sp (split-behind (c₁ j) (c₂ j)) ts h) g))
    core

canon-LR-sp
  : ∀ {x y : Ty} {As : List G.Ob} {Θ Γ Μ Δ Ξ Κ Ξ₁ Μ₂ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ₂ Δ₁ Κ)
    (pΞ : Ξ₁ ++ Δ₁ ≡ Ξ) (pΜ : Ξ₁ ++ Μ₂ ≡ Μ)
    (c₁ : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (pΞ i)) (split-++ˡ s₁' Δ₁) s₁)
    (c₂ : PathP (λ i → Split y (pΜ i) (pΞ i) Κ) (split-++ʳ Ξ₁ s₂') s₂)
    (ts : Sp (Γ₁ ++ Δ₁) As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
              (sub-sp (split-++ˡ s₁' Δ₁) ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
              (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) ts h) g)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub-sp s₁ ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
              (sub-sp (split-behind s₁ s₂) ts h) g)
canon-LR-sp {x = x} {As = As} {Θ = Θ} {Γ = Γ} {Δ = Δ} {Κ = Κ}
  s₁' s₂' pΞ pΜ c₁ c₂ ts g h core =
  transport
    (λ j → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ (pΜ j) Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (c₂ j))) (sub-sp (c₁ j) ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x (pΜ j)) (Δ ++ Κ))
              (sub-sp (split-behind (c₁ j) (c₂ j)) ts h) g))
    core

canon-RR-sp
  : ∀ {x y : Ty} {As : List G.Ob} {Θ Γ Μ Δ Ξ Κ Θ₂ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
    (s₁' : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    (c₁ : PathP (λ i → Split x (q i) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₁') s₁)
    (ts : Sp (Γ₁ ++ Δ₁) As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary (Γ₁ ++ Θ₂) Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂))
              (sub-sp (split-++ʳ Γ₁ s₁') ts g) h)
      (sub-sp (split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ))
              (sub-sp (split-behind (split-++ʳ Γ₁ s₁') s₂) ts h) g)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub-sp s₁ ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
              (sub-sp (split-behind s₁ s₂) ts h) g)
canon-RR-sp {x = x} {As = As} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Κ = Κ} {s₂ = s₂}
  s₁' q c₁ ts g h core =
  transport
    (λ j → PathP (λ i → Sp (interchangeₘ-boundary (q j) Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ (q j) (split-++ʳ Γ s₂)) (sub-sp (c₁ j) ts g) h)
      (sub-sp (split-++ˡ (split-here (q j) x Μ) (Δ ++ Κ))
              (sub-sp (split-behind (c₁ j) s₂) ts h) g))
    core

-- ==========================================================================
-- §7  The mutual induction.
--
-- Layout: the two top-level lemmas dispatch on the term constructor and hand
-- the two-slot view (§2) to a dispatcher per constructor; each dispatcher
-- canonicalises the splits (§6, or inline for the second-stage views of
-- match⊗/match𝟙) and invokes a core lemma in which every split is a literal
-- weakening of canonical component splits, so both sides reduce through
-- sub's handlers by the split-++-ˡ/ʳ computation rules.
-- ==========================================================================

sub-interchange
  : ∀ {x y z : Ty} {Θ Ρ Ξ Μ Κ Γ Δ : Ctx}
    (s₁ : Split x Θ Ρ Ξ) (s₂ : Split y Μ Ξ Κ)
    (t : Tm Ρ z) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) z)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ t g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) t h) g)

sub-sp-interchange
  : ∀ {x y : Ty} {Θ Ρ Ξ Μ Κ Γ Δ : Ctx} {As : List G.Ob}
    (s₁ : Split x Θ Ρ Ξ) (s₂ : Split y Μ Ξ Κ)
    (ts : Sp Ρ As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ Κ i) As)
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub-sp s₁ ts g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
              (sub-sp (split-behind s₁ s₂) ts h) g)

-- ---- pair ----------------------------------------------------------------

sub-pair-int
  : ∀ {x y A B : Ty} {Θ Γ Μ Δ Ξ Κ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Γ₁ Δ₁ s₁ s₂
  → (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) (A ⊗ B))
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ ⦅ P , Q ⦆ g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) ⦅ P , Q ⦆ h) g)

core-pair-LL
  : ∀ {x y A B : Ty} {Θ Γ Μ Δ Γ₁ Δ₁ Ξ₁ Κ₁ : Ctx}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁) i) (A ⊗ B))
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁)))
           (sub (split-++ˡ s₁' Δ₁) ⦅ P , Q ⦆ g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁))
           (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) ⦅ P , Q ⦆ h) g)

core-pair-LR
  : ∀ {x y A B : Ty} {Θ Γ Μ₂ Δ Κ Γ₁ Δ₁ Ξ₁ : Ctx}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ₂ Δ₁ Κ)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) (A ⊗ B))
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
           (sub (split-++ˡ s₁' Δ₁) ⦅ P , Q ⦆ g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) ⦅ P , Q ⦆ h) g)

core-pair-RR
  : ∀ {x y A B : Ty} {Θ₂ Γ Μ Δ Ξ Κ Γ₁ Δ₁ : Ctx}
    (s₁' : Split x Θ₂ Δ₁ Ξ) (s₂ : Split y Μ Ξ Κ)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γ₁ ++ Θ₂) Γ Μ Δ Κ i) (A ⊗ B))
      (sub (split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γ₁ s₁') ⦅ P , Q ⦆ g) h)
      (sub (split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γ₁ s₁') s₂) ⦅ P , Q ⦆ h) g)

-- ---- spine cons ----------------------------------------------------------

sub-cons-int
  : ∀ {x y : Ty} {A : G.Ob} {As : List G.Ob} {Θ Γ Μ Δ Ξ Κ Γ₁ Δ₁ : Ctx}
    {s₁ : Split x Θ (Γ₁ ++ Δ₁) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Γ₁ Δ₁ s₁ s₂
  → (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ Κ i) (A ∷ As))
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub-sp s₁ (t ∷ ts) g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
              (sub-sp (split-behind s₁ s₂) (t ∷ ts) h) g)

core-cons-LL
  : ∀ {x y : Ty} {A : G.Ob} {As : List G.Ob} {Θ Γ Μ Δ Γ₁ Δ₁ Ξ₁ Κ₁ : Ctx}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Δ₁) i) (A ∷ As))
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁)))
              (sub-sp (split-++ˡ s₁' Δ₁) (t ∷ ts) g) h)
      (sub-sp (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁))
              (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) (t ∷ ts) h) g)

core-cons-LR
  : ∀ {x y : Ty} {A : G.Ob} {As : List G.Ob} {Θ Γ Μ₂ Δ Κ Γ₁ Δ₁ Ξ₁ : Ctx}
    (s₁' : Split x Θ Γ₁ Ξ₁) (s₂' : Split y Μ₂ Δ₁ Κ)
    (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) (A ∷ As))
      (sub-sp (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
              (sub-sp (split-++ˡ s₁' Δ₁) (t ∷ ts) g) h)
      (sub-sp (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
              (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) (t ∷ ts) h) g)

core-cons-RR
  : ∀ {x y : Ty} {A : G.Ob} {As : List G.Ob} {Θ₂ Γ Μ Δ Ξ Κ Γ₁ Δ₁ : Ctx}
    (s₁' : Split x Θ₂ Δ₁ Ξ) (s₂ : Split y Μ Ξ Κ)
    (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Sp (interchangeₘ-boundary (Γ₁ ++ Θ₂) Γ Μ Δ Κ i) (A ∷ As))
      (sub-sp (split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂))
              (sub-sp (split-++ʳ Γ₁ s₁') (t ∷ ts) g) h)
      (sub-sp (split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ))
              (sub-sp (split-behind (split-++ʳ Γ₁ s₁') s₂) (t ∷ ts) h) g)

-- ---- match⊗ --------------------------------------------------------------

sub-match⊗-int
  : ∀ {x y A B C : Ty} {Θ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    {s₁ : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Γm (Ψ ++ Δm) s₁ s₂
  → (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂))
           (sub s₁ (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

-- x in Γm, y somewhere in Ψ ++ Δm: second view on the y-slot.
sub-match⊗-intˣ
  : ∀ {x y A B C : Ty} {Θ Γ Μ₂ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    {s₂' : Split y Μ₂ (Ψ ++ Δm) Κ}
  → Split-++ Ψ Δm s₂'
  → (s₁' : Split x Θ Γm Ξ₁)
  → (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ s₂'))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

-- x (hence also y) in Ψ ++ Δm: second two-slot view.
sub-match⊗-intʳ
  : ∀ {x y A B C : Ty} {Θ₂ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    {s₁' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Ψ Δm s₁' s₂
  → (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm s₁') (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm s₁') s₂)
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΓΓ
  : ∀ {x y A B C : Ty} {Θ Γ Μ Δ Ψ Γm Δm Ξ₁ Κ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Ψ ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' (Ψ ++ Δm))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Ψ ++ Δm))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ˡ s₂' (Ψ ++ Δm)))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΓΨ
  : ∀ {x y A B C : Ty} {Θ Γ Μ₂ Δ Κᵧ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂ᵧ : Split y Μ₂ Ψ Κᵧ)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ (Κᵧ ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (split-++ˡ s₂ᵧ Δm))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κᵧ ++ Δm))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (split-++ˡ s₂ᵧ Δm)))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΓΔ
  : ∀ {x y A B C : Ty} {Θ Γ Μᵧ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂ᵧ : Split y Μᵧ Δm Κ)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Ψ ++ Μᵧ) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (split-++ʳ Ψ s₂ᵧ))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Ψ ++ Μᵧ)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (split-++ʳ Ψ s₂ᵧ)))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΨΨ
  : ∀ {x y A B C : Ty} {Θ₂ Γ Μ Δ Ψ Γm Δm Ξ₁ Κ₁ : Ctx}
    (s₁'' : Split x Θ₂ Ψ Ξ₁) (s₂'' : Split y Μ Ξ₁ Κ₁)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ (Κ₁ ++ Δm) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ˡ s₂'' Δm)))
           (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ₁ ++ Δm))
           (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ˡ s₂'' Δm))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΨΔ
  : ∀ {x y A B C : Ty} {Θ₂ Γ Μᵧ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁'' : Split x Θ₂ Ψ Ξ₁) (s₂ᵧ : Split y Μᵧ Δm Κ)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ (Ξ₁ ++ Μᵧ) Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᵧ)))
           (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x (Ξ₁ ++ Μᵧ)) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m⊗-ΔΔ
  : ∀ {x y A B C : Ty} {Θ₃ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    (s₁'' : Split x Θ₃ Δm Ξ) (s₂ : Split y Μ Ξ Κ)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Ψ ++ Θ₃) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Ψ ++ Θ₃) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm (split-++ʳ Ψ s₁'')) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Ψ ++ Θ₃) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (split-++ʳ Ψ s₁'')) s₂)
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)

-- ---- match𝟙 --------------------------------------------------------------

sub-match𝟙-int
  : ∀ {x y C : Ty} {Θ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    {s₁ : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Γm (Ψ ++ Δm) s₁ s₂
  → (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂))
           (sub s₁ (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

sub-match𝟙-intˣ
  : ∀ {x y C : Ty} {Θ Γ Μ₂ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    {s₂' : Split y Μ₂ (Ψ ++ Δm) Κ}
  → Split-++ Ψ Δm s₂'
  → (s₁' : Split x Θ Γm Ξ₁)
  → (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂')))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ s₂'))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

sub-match𝟙-intʳ
  : ∀ {x y C : Ty} {Θ₂ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    {s₁' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s₂ : Split y Μ Ξ Κ}
  → Split²-++ Ψ Δm s₁' s₂
  → (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm s₁') (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm s₁') s₂)
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΓΓ
  : ∀ {x y C : Ty} {Θ Γ Μ Δ Ψ Γm Δm Ξ₁ Κ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂' : Split y Μ Ξ₁ Κ₁)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ Ψ ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' (Ψ ++ Δm))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Ψ ++ Δm))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ˡ s₂' (Ψ ++ Δm)))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΓΨ
  : ∀ {x y C : Ty} {Θ Γ Μ₂ Δ Κᵧ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂ᵧ : Split y Μ₂ Ψ Κᵧ)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ (Κᵧ ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (split-++ˡ s₂ᵧ Δm))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κᵧ ++ Δm))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (split-++ˡ s₂ᵧ Δm)))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΓΔ
  : ∀ {x y C : Ty} {Θ Γ Μᵧ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁' : Split x Θ Γm Ξ₁) (s₂ᵧ : Split y Μᵧ Δm Κ)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Ψ ++ Μᵧ) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (split-++ʳ Ψ s₂ᵧ))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Ψ ++ Μᵧ)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (split-++ʳ Ψ s₂ᵧ)))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΨΨ
  : ∀ {x y C : Ty} {Θ₂ Γ Μ Δ Ψ Γm Δm Ξ₁ Κ₁ : Ctx}
    (s₁'' : Split x Θ₂ Ψ Ξ₁) (s₂'' : Split y Μ Ξ₁ Κ₁)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ (Κ₁ ++ Δm) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ˡ s₂'' Δm)))
           (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ₁ ++ Δm))
           (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ˡ s₂'' Δm))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΨΔ
  : ∀ {x y C : Ty} {Θ₂ Γ Μᵧ Δ Κ Ψ Γm Δm Ξ₁ : Ctx}
    (s₁'' : Split x Θ₂ Ψ Ξ₁) (s₂ᵧ : Split y Μᵧ Δm Κ)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ (Ξ₁ ++ Μᵧ) Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᵧ)))
           (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x (Ξ₁ ++ Μᵧ)) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

core-m𝟙-ΔΔ
  : ∀ {x y C : Ty} {Θ₃ Γ Μ Δ Ξ Κ Ψ Γm Δm : Ctx}
    (s₁'' : Split x Θ₃ Δm Ξ) (s₂ : Split y Μ Ξ Κ)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Ψ ++ Θ₃) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Ψ ++ Θ₃) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm (split-++ʳ Ψ s₁'')) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Ψ ++ Θ₃) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (split-++ʳ Ψ s₁'')) s₂)
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)

-- ---- top-level dispatch ---------------------------------------------------

-- t = var forces a singleton carrier, so one of the two slots points into
-- the empty context (a standalone helper, so that sub-interchange itself
-- always matches the term first — same design note as sub-var).
sub-interchange-var
  : ∀ {x y A : Ty} {Θ Ξ Μ Κ Γ Δ : Ctx}
    (s₁ : Split x Θ (A ∷ []) Ξ) (s₂ : Split y Μ Ξ Κ)
    (g : Tm Γ x) (h : Tm Δ y)
  → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ Μ Δ Κ i) A)
      (sub (split-++ʳ Θ (split-++ʳ Γ s₂)) (sub s₁ var g) h)
      (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ))
           (sub (split-behind s₁ s₂) var h) g)
sub-interchange-var here       s₂ g h = absurd (split-[] s₂)
sub-interchange-var (there s₁) s₂ g h = absurd (split-[] s₁)

sub-interchange s₁ s₂ var g h = sub-interchange-var s₁ s₂ g h
sub-interchange s₁ s₂ (gen f sp) g h i = gen f (sub-sp-interchange s₁ s₂ sp g h i)
sub-interchange s₁ s₂ (⦅_,_⦆ {Γ = Γ₁} P Q) g h = sub-pair-int (view² Γ₁ s₁ s₂) P Q g h
sub-interchange s₁ s₂ (match⊗ {Γ = Γm} P Q) g h = sub-match⊗-int (view² Γm s₁ s₂) P Q g h
sub-interchange s₁ s₂ ⋆ g h = absurd (split-[] s₁)
sub-interchange s₁ s₂ (match𝟙 {Γ = Γm} P Q) g h = sub-match𝟙-int (view² Γm s₁ s₂) P Q g h

sub-sp-interchange s₁ s₂ [] g h = absurd (split-[] s₁)
sub-sp-interchange s₁ s₂ (_∷_ {Γ = Γ₁} t ts) g h = sub-cons-int (view² Γ₁ s₁ s₂) t ts g h

-- ---- pair/cons dispatch ---------------------------------------------------

sub-pair-int (both-left s₁' s₂' pΞ pΚ c₁ c₂) P Q g h =
  canon-LL s₁' s₂' pΞ pΚ c₁ c₂ ⦅ P , Q ⦆ g h (core-pair-LL s₁' s₂' P Q g h)
sub-pair-int (cross s₁' s₂' pΞ pΜ c₁ c₂) P Q g h =
  canon-LR s₁' s₂' pΞ pΜ c₁ c₂ ⦅ P , Q ⦆ g h (core-pair-LR s₁' s₂' P Q g h)
sub-pair-int (both-right s₁' q c₁) P Q g h =
  canon-RR s₁' q c₁ ⦅ P , Q ⦆ g h (core-pair-RR s₁' _ P Q g h)

sub-cons-int (both-left s₁' s₂' pΞ pΚ c₁ c₂) t ts g h =
  canon-LL-sp s₁' s₂' pΞ pΚ c₁ c₂ (t ∷ ts) g h (core-cons-LL s₁' s₂' t ts g h)
sub-cons-int (cross s₁' s₂' pΞ pΜ c₁ c₂) t ts g h =
  canon-LR-sp s₁' s₂' pΞ pΜ c₁ c₂ (t ∷ ts) g h (core-cons-LR s₁' s₂' t ts g h)
sub-cons-int (both-right s₁' q c₁) t ts g h =
  canon-RR-sp s₁' q c₁ (t ∷ ts) g h (core-cons-RR s₁' _ t ts g h)

-- ---- match⊗ dispatch ------------------------------------------------------

sub-match⊗-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (both-left s₁' s₂' pΞ pΚ c₁ c₂) P Q g h =
  canon-LL s₁' s₂' pΞ pΚ c₁ c₂ (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h
    (core-m⊗-ΓΓ {Γm = Γm} {Δm = Δm} s₁' s₂' P Q g h)
sub-match⊗-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (cross s₁' s₂' pΞ pΜ c₁ c₂) P Q g h =
  canon-LR s₁' s₂' pΞ pΜ c₁ c₂ (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h
    (sub-match⊗-intˣ (split-++ Ψ s₂') s₁' P Q g h)
sub-match⊗-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (both-right s₁' q c₁) P Q g h =
  canon-RR s₁' q c₁ (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h
    (sub-match⊗-intʳ (view² Ψ s₁' _) P Q g h)

sub-match⊗-intˣ {x = x} {C = C} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁}
  (on-left {Ξ₁ = Κᵧ} s₂ᵧ p co) s₁' P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ (p j) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (co j))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ p j))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (co j)))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m⊗-ΓΨ {Γm = Γm} {Δm = Δm} s₁' s₂ᵧ P Q g h)
sub-match⊗-intˣ {x = x} {C = C} {Θ = Θ} {Γ = Γ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁}
  (on-right {Θ₂ = Μᵧ} s₂ᵧ q co) s₁' P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ q j) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (co j))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ q j)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (co j)))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m⊗-ΓΔ {Γm = Γm} {Δm = Δm} s₁' s₂ᵧ P Q g h)

sub-match⊗-intʳ {x = x} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Γm = Γm} {Δm = Δm}
  (both-left s₁'' s₂'' pΞ pΚ c₁ c₂) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ (pΚ j) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (c₂ j)))
           (sub (split-++ʳ Γm (c₁ j)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ pΚ j))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) (c₂ j))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m⊗-ΨΨ {Γm = Γm} {Δm = Δm} s₁'' s₂'' P Q g h)
sub-match⊗-intʳ {x = x} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Δ = Δ} {Κ = Κ} {Γm = Γm} {Δm = Δm}
  (cross s₁'' s₂ᵧ pΞ pΜ c₁ c₂) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ (pΜ j) Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (c₂ j)))
           (sub (split-++ʳ Γm (c₁ j)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x (pΜ j)) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) (c₂ j))
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m⊗-ΨΔ {Γm = Γm} {Δm = Δm} s₁'' s₂ᵧ P Q g h)
sub-match⊗-intʳ {x = x} {C = C} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Κ = Κ} {Γm = Γm} {Δm = Δm} {s₂ = s₂}
  (both-right s₁'' q c₁) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ q j) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ q j) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm (c₁ j)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ q j) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) s₂)
                (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m⊗-ΔΔ {Γm = Γm} {Δm = Δm} s₁'' s₂ P Q g h)

-- ---- match𝟙 dispatch ------------------------------------------------------

sub-match𝟙-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (both-left s₁' s₂' pΞ pΚ c₁ c₂) P Q g h =
  canon-LL s₁' s₂' pΞ pΚ c₁ c₂ (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h
    (core-m𝟙-ΓΓ {Γm = Γm} {Δm = Δm} s₁' s₂' P Q g h)
sub-match𝟙-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (cross s₁' s₂' pΞ pΜ c₁ c₂) P Q g h =
  canon-LR s₁' s₂' pΞ pΜ c₁ c₂ (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h
    (sub-match𝟙-intˣ (split-++ Ψ s₂') s₁' P Q g h)
sub-match𝟙-int {Ψ = Ψ} {Γm = Γm} {Δm = Δm} (both-right s₁' q c₁) P Q g h =
  canon-RR s₁' q c₁ (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h
    (sub-match𝟙-intʳ (view² Ψ s₁' _) P Q g h)

sub-match𝟙-intˣ {x = x} {C = C} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁}
  (on-left {Ξ₁ = Κᵧ} s₂ᵧ p co) s₁' P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Μ₂) Δ (p j) i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (co j))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ p j))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (co j)))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m𝟙-ΓΨ {Γm = Γm} {Δm = Δm} s₁' s₂ᵧ P Q g h)
sub-match𝟙-intˣ {x = x} {C = C} {Θ = Θ} {Γ = Γ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁}
  (on-right {Θ₂ = Μᵧ} s₂ᵧ q co) s₁' P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary Θ Γ (Ξ₁ ++ q j) Δ Κ i) C)
      (sub (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ (co j))))
           (sub (split-++ˡ s₁' (Ψ ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here Θ x (Ξ₁ ++ q j)) (Δ ++ Κ))
           (sub (split-behind (split-++ˡ s₁' (Ψ ++ Δm)) (split-++ʳ Ξ₁ (co j)))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m𝟙-ΓΔ {Γm = Γm} {Δm = Δm} s₁' s₂ᵧ P Q g h)

sub-match𝟙-intʳ {x = x} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Γm = Γm} {Δm = Δm}
  (both-left s₁'' s₂'' pΞ pΚ c₁ c₂) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ Μ Δ (pΚ j) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (c₂ j)))
           (sub (split-++ʳ Γm (c₁ j)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ pΚ j))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) (c₂ j))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m𝟙-ΨΨ {Γm = Γm} {Δm = Δm} s₁'' s₂'' P Q g h)
sub-match𝟙-intʳ {x = x} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Δ = Δ} {Κ = Κ} {Γm = Γm} {Δm = Δm}
  (cross s₁'' s₂ᵧ pΞ pΜ c₁ c₂) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ Θ₂) Γ (pΜ j) Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (c₂ j)))
           (sub (split-++ʳ Γm (c₁ j)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ Θ₂) x (pΜ j)) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) (c₂ j))
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m𝟙-ΨΔ {Γm = Γm} {Δm = Δm} s₁'' s₂ᵧ P Q g h)
sub-match𝟙-intʳ {x = x} {C = C} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Κ = Κ} {Γm = Γm} {Δm = Δm} {s₂ = s₂}
  (both-right s₁'' q c₁) P Q g h =
  transport
    (λ j → PathP (λ i → Tm (interchangeₘ-boundary (Γm ++ q j) Γ Μ Δ Κ i) C)
      (sub (split-++ʳ (Γm ++ q j) (split-++ʳ Γ s₂))
           (sub (split-++ʳ Γm (c₁ j)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ (split-here (Γm ++ q j) x Μ) (Δ ++ Κ))
           (sub (split-behind (split-++ʳ Γm (c₁ j)) s₂)
                (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g))
    (core-m𝟙-ΔΔ {Γm = Γm} {Δm = Δm} s₁'' s₂ P Q g h)

-- ---- core lemmas (to be filled) -------------------------------------------

core-pair-LL {x = x} {y = y} {A = A} {B = B} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁' s₂' P Q g h =
  tm-over (sq-LL Θ Γ Μ Δ Κ₁ Δ₁) (eL ◁ seg₃ ▷ sym eR)
  where
    TmΩ : Ctx → Type _
    TmΩ Ω = Tm Ω (A ⊗ B)

    bdΚ : (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΚ = interchangeₘ-boundary Θ Γ Μ Δ Κ₁

    flL : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ₁)
    flL = flattenˡ Θ Γ Ξ₁ Δ₁

    flΜ : (Μ ++ Δ ++ Κ₁) ++ Δ₁ ≡ Μ ++ Δ ++ (Κ₁ ++ Δ₁)
    flΜ = flattenˡ Μ Δ Κ₁ Δ₁

    qL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ Δ₁ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)
    qL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ Δ₁

    qR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ Δ₁ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ Δ₁)
    qR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) Δ₁

    pR : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)
    pR = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ Δ₁

    S : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ Δ₁)) (Κ₁ ++ Δ₁)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁))

    S₀ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ Ξ₁) Κ₁
    S₀ = split-++ʳ Θ (split-++ʳ Γ s₂')

    Sᶜ : Split y (Θ ++ Γ ++ Μ) ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (Κ₁ ++ Δ₁)
    Sᶜ = split-++ˡ S₀ Δ₁

    W₁ : Tm (Θ ++ Γ ++ Ξ₁) A
    W₁ = sub s₁' P g

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (A ⊗ B)
    W = ⦅ W₁ , Q ⦆

    ihL : Tm ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) A
    ihL = sub S₀ W₁ h

    SB : Split y (Θ ++ x ∷ Μ) Γ₁ Κ₁
    SB = split-behind s₁' s₂'

    SR₁ : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁)

    ihR : Tm (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) A
    ihR = sub SR₁ (sub SB P h) g

    ih : PathP (λ i → Tm (bdΚ i) A) ihL ihR
    ih = sub-interchange s₁' s₂' P g h

    V : Tm (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁) (A ⊗ B)
    V = ⦅ sub SB P h , Q ⦆

    SR : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)) (Μ ++ Δ ++ (Κ₁ ++ Δ₁))
    SR = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁)

    SRᶜ : Split x Θ (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁) ((Μ ++ Δ ++ Κ₁) ++ Δ₁)
    SRᶜ = split-++ˡ SR₁ Δ₁

    eL : sub S (sub (split-++ˡ s₁' Δ₁) ⦅ P , Q ⦆ g) h ≡ cast qL ⦅ ihL , Q ⦆
    eL = ap (λ v → sub S (sub-pair v P Q g) h) (split-++-ˡ s₁' Δ₁)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flL)
       ∙ sym (λ i → sub (co-ʳʳˡ Θ Γ s₂' Δ₁ i) (cast-filler flL W i) h)
       ∙ ap (λ v → sub-pair v W₁ Q h) (split-++-ˡ S₀ Δ₁)
       ∙ cast-∙idr qL ⦅ ihL , Q ⦆

    eR : sub SR (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) ⦅ P , Q ⦆ h) g
       ≡ sub SR (cast pR V) g
    eR = ap (λ s → sub SR (sub s ⦅ P , Q ⦆ h) g) (split-behind-++ˡ s₁' s₂' Δ₁)
       ∙ ap (λ v → sub SR (sub-pair v P Q h) g) (split-++-ˡ SB Δ₁)
       ∙ ap (λ ρ → sub SR (cast ρ V) g) (∙-idr pR)

    eV : sub SRᶜ V g ≡ cast qR ⦅ ihR , Q ⦆
    eV = ap (λ v → sub-pair v (sub SB P h) Q g) (split-++-ˡ SR₁ Δ₁)
       ∙ cast-∙idr qR ⦅ ihR , Q ⦆

    π' : PathP (λ i → Tm (Θ ++ Γ ++ flΜ i) (A ⊗ B))
           (sub SRᶜ V g) (sub SR (cast pR V) g)
    π' i = sub (co-hereˡ Θ x Μ Δ Κ₁ Δ₁ i) (cast-filler pR V i) g

    seg₁ : PathP (λ i → TmΩ ((sym qL ∙ ap (_++ Δ₁) bdΚ) i))
             (cast qL ⦅ ihL , Q ⦆) ⦅ ihR , Q ⦆
    seg₁ = _∙P_ {B = TmΩ} {p = sym qL} {q = ap (_++ Δ₁) bdΚ}
             (symP (cast-filler qL ⦅ ihL , Q ⦆))
             (λ i → ⦅ ih i , Q ⦆)

    seg₂ : PathP (λ i → TmΩ (((sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR) i))
             (cast qL ⦅ ihL , Q ⦆) (sub SRᶜ V g)
    seg₂ = _∙P_ {B = TmΩ} {p = sym qL ∙ ap (_++ Δ₁) bdΚ} {q = qR}
             seg₁ (cast-filler qR ⦅ ihR , Q ⦆)
           ▷ sym eV

    seg₃ : PathP (λ i → TmΩ ((((sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flΜ) i))
             (cast qL ⦅ ihL , Q ⦆) (sub SR (cast pR V) g)
    seg₃ = _∙P_ {B = TmΩ} {p = (sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR}
             {q = ap (λ l → Θ ++ Γ ++ l) flΜ}
             seg₂ π'
core-pair-LR {x = x} {y = y} {A = A} {B = B} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Κ = Κ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Ξ₁ = Ξ₁} s₁' s₂' P Q g h =
  tm-over (sq-LR Θ Γ Ξ₁ Μ₂ Δ Κ) (e₁ ◁ seg₃)
  where
    TmΩ : Ctx → Type _
    TmΩ Ω = Tm Ω (A ⊗ B)

    flΔ : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ₁)
    flΔ = flattenˡ Θ Γ Ξ₁ Δ₁

    flΜ₂ : (Θ ++ Γ ++ Ξ₁) ++ Μ₂ ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂)
    flΜ₂ = flattenˡ Θ Γ Ξ₁ Μ₂

    flʳΞ : Ξ₁ ++ (Μ₂ ++ Δ ++ Κ) ≡ (Ξ₁ ++ Μ₂) ++ Δ ++ Κ
    flʳΞ = flattenʳ Ξ₁ Μ₂ Δ Κ

    qL : (Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ) ≡ ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ++ Δ ++ Κ
    qL = flattenʳ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κ

    qR : (Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ) ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂ ++ Δ ++ Κ)
    qR = flattenˡ Θ Γ Ξ₁ (Μ₂ ++ Δ ++ Κ)

    pRc : Γ₁ ++ (Μ₂ ++ Δ ++ Κ) ≡ (Γ₁ ++ Μ₂) ++ Δ ++ Κ
    pRc = flattenʳ Γ₁ Μ₂ Δ Κ

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Μ₂)) (Θ ++ Γ ++ (Ξ₁ ++ Δ₁)) Κ
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂'))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) Κ
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂'

    W₁ : Tm (Θ ++ Γ ++ Ξ₁) A
    W₁ = sub s₁' P g

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (A ⊗ B)
    W = ⦅ W₁ , Q ⦆

    X₂ : Tm (Μ₂ ++ Δ ++ Κ) B
    X₂ = sub s₂' Q h

    X : Tm ((Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ)) (A ⊗ B)
    X = ⦅ W₁ , X₂ ⦆

    V : Tm (Γ₁ ++ (Μ₂ ++ Δ ++ Κ)) (A ⊗ B)
    V = ⦅ P , X₂ ⦆

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Μ₂)) ++ Δ ++ Κ) ((Ξ₁ ++ Μ₂) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ)

    SR₀ : Split x Θ ((Γ₁ ++ Μ₂) ++ Δ ++ Κ) ((Ξ₁ ++ Μ₂) ++ Δ ++ Κ)
    SR₀ = split-++ˡ (split-++ˡ s₁' Μ₂) (Δ ++ Κ)

    SRᶜ : Split x Θ (Γ₁ ++ (Μ₂ ++ Δ ++ Κ)) (Ξ₁ ++ (Μ₂ ++ Δ ++ Κ))
    SRᶜ = split-++ˡ s₁' (Μ₂ ++ Δ ++ Κ)

    e₁ : sub S (sub (split-++ˡ s₁' Δ₁) ⦅ P , Q ⦆ g) h ≡ sub S (cast flΔ W) h
    e₁ = ap (λ v → sub S (sub-pair v P Q g) h) (split-++-ˡ s₁' Δ₁)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΔ)

    ℓ₂ : PathP (λ i → Tm (flΜ₂ i ++ Δ ++ Κ) (A ⊗ B))
           (sub Sᶜ W h) (sub S (cast flΔ W) h)
    ℓ₂ i = sub (co-crossˡ Θ Γ Ξ₁ s₂' i) (cast-filler flΔ W i) h

    e₂ : sub Sᶜ W h ≡ cast qL X
    e₂ = ap (λ v → sub-pair v W₁ Q h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂')
       ∙ cast-∙idr qL X

    e₃ : sub SR₀ (sub (split-++ʳ Γ₁ s₂') ⦅ P , Q ⦆ h) g ≡ sub SR₀ (cast pRc V) g
    e₃ = ap (λ v → sub SR₀ (sub-pair v P Q h) g) (split-++-ʳ Γ₁ s₂')
       ∙ ap (λ ρ → sub SR₀ (cast ρ V) g) (∙-idr pRc)

    e₄ : sub SRᶜ V g ≡ cast qR X
    e₄ = ap (λ v → sub-pair v P X₂ g) (split-++-ˡ s₁' (Μ₂ ++ Δ ++ Κ))
       ∙ cast-∙idr qR X

    π' : PathP (λ i → Tm (Θ ++ Γ ++ flʳΞ i) (A ⊗ B))
           (sub SRᶜ V g) (sub SR₀ (cast pRc V) g)
    π' i = sub (co-crossʳ s₁' Μ₂ Δ Κ i) (cast-filler pRc V i) g

    e₅ : sub SR₀ (sub (split-++ʳ Γ₁ s₂') ⦅ P , Q ⦆ h) g
       ≡ sub SR (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) ⦅ P , Q ⦆ h) g
    e₅ j = sub (co-crossʰ s₁' Μ₂ (Δ ++ Κ) j)
               (sub (split-behind-cross s₁' s₂' j) ⦅ P , Q ⦆ h) g

    seg₁ : PathP (λ i → TmΩ ((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) i))
             (sub S (cast flΔ W) h) X
    seg₁ = _∙P_ {B = TmΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ₂)} {q = sym qL}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qL X))

    seg₂ : PathP (λ i → TmΩ (((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR) i))
             (sub S (cast flΔ W) h) (sub SRᶜ V g)
    seg₂ = _∙P_ {B = TmΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL} {q = qR}
             seg₁ (cast-filler qR X)
           ▷ sym e₄

    seg₃ : PathP (λ i → TmΩ ((((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flʳΞ) i))
             (sub S (cast flΔ W) h)
             (sub SR (sub (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) ⦅ P , Q ⦆ h) g)
    seg₃ = _∙P_ {B = TmΩ} {p = (sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR}
             {q = ap (λ l → Θ ++ Γ ++ l) flʳΞ}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-pair-RR {x = x} {y = y} {A = A} {B = B} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ξ = Ξ} {Κ = Κ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} s₁' s₂ P Q g h =
  tm-over (sq-RR Γ₁ Θ₂ Γ Μ Δ Κ) (e₁ ◁ seg₃)
  where
    TmΩ : Ctx → Type _
    TmΩ Ω = Tm Ω (A ⊗ B)

    bdΘ : (Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdΘ = interchangeₘ-boundary Θ₂ Γ Μ Δ Κ

    pL : Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
    pL = flattenʳ Γ₁ Θ₂ Γ Ξ

    flΜ : Γ₁ ++ (Θ₂ ++ Γ ++ Μ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Μ
    flΜ = flattenʳ Γ₁ Θ₂ Γ Μ

    qL : Γ₁ ++ ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ) ≡ (Γ₁ ++ (Θ₂ ++ Γ ++ Μ)) ++ Δ ++ Κ
    qL = flattenʳ Γ₁ (Θ₂ ++ Γ ++ Μ) Δ Κ

    qR : Γ₁ ++ (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ (Μ ++ Δ ++ Κ)
    qR = flattenʳ Γ₁ Θ₂ Γ (Μ ++ Δ ++ Κ)

    pR : Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ) ≡ (Γ₁ ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ Κ
    pR = flattenʳ Γ₁ (Θ₂ ++ x ∷ Μ) Δ Κ

    S : Split y ((Γ₁ ++ Θ₂) ++ Γ ++ Μ) ((Γ₁ ++ Θ₂) ++ Γ ++ Ξ) Κ
    S = split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂)

    S₀ : Split y (Θ₂ ++ Γ ++ Μ) (Θ₂ ++ Γ ++ Ξ) Κ
    S₀ = split-++ʳ Θ₂ (split-++ʳ Γ s₂)

    Sᶜ : Split y (Γ₁ ++ (Θ₂ ++ Γ ++ Μ)) (Γ₁ ++ (Θ₂ ++ Γ ++ Ξ)) Κ
    Sᶜ = split-++ʳ Γ₁ S₀

    W₂ : Tm (Θ₂ ++ Γ ++ Ξ) B
    W₂ = sub s₁' Q g

    W : Tm (Γ₁ ++ (Θ₂ ++ Γ ++ Ξ)) (A ⊗ B)
    W = ⦅ P , W₂ ⦆

    ihL : Tm ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ) B
    ihL = sub S₀ W₂ h

    SB : Split y (Θ₂ ++ x ∷ Μ) Δ₁ Κ
    SB = split-behind s₁' s₂

    SR₁ : Split x Θ₂ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR₁ = split-++ˡ (split-here Θ₂ x Μ) (Δ ++ Κ)

    ihR : Tm (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)) B
    ihR = sub SR₁ (sub SB Q h) g

    ih : PathP (λ i → Tm (bdΘ i) B) ihL ihR
    ih = sub-interchange s₁' s₂ Q g h

    V : Tm (Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ)) (A ⊗ B)
    V = ⦅ P , sub SB Q h ⦆

    SR : Split x (Γ₁ ++ Θ₂) (((Γ₁ ++ Θ₂) ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ)

    SR' : Split x (Γ₁ ++ Θ₂) ((Γ₁ ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR' = split-++ˡ (split-++ʳ Γ₁ (split-here Θ₂ x Μ)) (Δ ++ Κ)

    SRᶜ : Split x (Γ₁ ++ Θ₂) (Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ)) (Μ ++ Δ ++ Κ)
    SRᶜ = split-++ʳ Γ₁ SR₁

    e₁ : sub S (sub (split-++ʳ Γ₁ s₁') ⦅ P , Q ⦆ g) h ≡ sub S (cast pL W) h
    e₁ = ap (λ v → sub S (sub-pair v P Q g) h) (split-++-ʳ Γ₁ s₁')
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr pL)

    ℓ₂ : PathP (λ i → Tm (flΜ i ++ Δ ++ Κ) (A ⊗ B))
           (sub Sᶜ W h) (sub S (cast pL W) h)
    ℓ₂ i = sub (co-ʳʳʳ Γ₁ Θ₂ Γ s₂ i) (cast-filler pL W i) h

    e₂ : sub Sᶜ W h ≡ cast qL ⦅ P , ihL ⦆
    e₂ = ap (λ v → sub-pair v P W₂ h) (split-++-ʳ Γ₁ S₀)
       ∙ cast-∙idr qL ⦅ P , ihL ⦆

    eV : sub SRᶜ V g ≡ cast qR ⦅ P , ihR ⦆
    eV = ap (λ v → sub-pair v P (sub SB Q h) g) (split-++-ʳ Γ₁ SR₁)
       ∙ cast-∙idr qR ⦅ P , ihR ⦆

    π' : sub SRᶜ V g ≡ sub SR' (cast pR V) g
    π' i = sub (co-hereʳ Γ₁ Θ₂ x Μ Δ Κ i) (cast-filler pR V i) g

    eR : sub SR (sub (split-behind (split-++ʳ Γ₁ s₁') s₂) ⦅ P , Q ⦆ h) g
       ≡ sub SR' (cast pR V) g
    eR = (λ j → sub (split-++ˡ (symP (split-here-++ʳ Γ₁ Θ₂ x Μ) j) (Δ ++ Κ))
                    (sub (split-behind-++ʳ Γ₁ s₁' s₂ j) ⦅ P , Q ⦆ h) g)
       ∙ ap (λ v → sub SR' (sub-pair v P Q h) g) (split-++-ʳ Γ₁ SB)
       ∙ ap (λ ρ → sub SR' (cast ρ V) g) (∙-idr pR)

    seg₁ : PathP (λ i → TmΩ ((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL) i))
             (sub S (cast pL W) h) ⦅ P , ihL ⦆
    seg₁ = _∙P_ {B = TmΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ)} {q = sym qL}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qL ⦅ P , ihL ⦆))

    seg₂ : PathP (λ i → TmΩ (((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                              ∙ ap (Γ₁ ++_) bdΘ) i))
             (sub S (cast pL W) h) ⦅ P , ihR ⦆
    seg₂ = _∙P_ {B = TmΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL}
             {q = ap (Γ₁ ++_) bdΘ}
             seg₁ (λ i → ⦅ P , ih i ⦆)

    seg₃ : PathP (λ i → TmΩ ((((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                               ∙ ap (Γ₁ ++_) bdΘ) ∙ qR) i))
             (sub S (cast pL W) h)
             (sub SR (sub (split-behind (split-++ʳ Γ₁ s₁') s₂) ⦅ P , Q ⦆ h) g)
    seg₃ = _∙P_ {B = TmΩ} {p = (sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                               ∙ ap (Γ₁ ++_) bdΘ} {q = qR}
             seg₂ (cast-filler qR ⦅ P , ihR ⦆)
           ▷ (sym eV ∙ π' ∙ sym eR)
core-cons-LL {x = x} {y = y} {A = A} {As = As} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁' s₂' t ts g h =
  sp-over (sq-LL Θ Γ Μ Δ Κ₁ Δ₁) (eL ◁ seg₃ ▷ sym eR)
  where
    SpΩ : Ctx → Type _
    SpΩ Ω = Sp Ω (A ∷ As)

    bdΚ : (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΚ = interchangeₘ-boundary Θ Γ Μ Δ Κ₁

    flL : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ₁)
    flL = flattenˡ Θ Γ Ξ₁ Δ₁

    flΜ : (Μ ++ Δ ++ Κ₁) ++ Δ₁ ≡ Μ ++ Δ ++ (Κ₁ ++ Δ₁)
    flΜ = flattenˡ Μ Δ Κ₁ Δ₁

    qL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ Δ₁ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)
    qL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ Δ₁

    qR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ Δ₁ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ Δ₁)
    qR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) Δ₁

    pR : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)
    pR = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ Δ₁

    S : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ Δ₁)) (Κ₁ ++ Δ₁)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' Δ₁))

    S₀ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ Ξ₁) Κ₁
    S₀ = split-++ʳ Θ (split-++ʳ Γ s₂')

    Sᶜ : Split y (Θ ++ Γ ++ Μ) ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (Κ₁ ++ Δ₁)
    Sᶜ = split-++ˡ S₀ Δ₁

    W₁ : Tm (Θ ++ Γ ++ Ξ₁) (base A)
    W₁ = sub s₁' t g

    W : Sp ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (A ∷ As)
    W = W₁ ∷ ts

    ihL : Tm ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) (base A)
    ihL = sub S₀ W₁ h

    SB : Split y (Θ ++ x ∷ Μ) Γ₁ Κ₁
    SB = split-behind s₁' s₂'

    SR₁ : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁)

    ihR : Tm (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) (base A)
    ihR = sub SR₁ (sub SB t h) g

    ih : PathP (λ i → Tm (bdΚ i) (base A)) ihL ihR
    ih = sub-interchange s₁' s₂' t g h

    V : Sp (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁) (A ∷ As)
    V = sub SB t h ∷ ts

    SR : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δ₁)) (Μ ++ Δ ++ (Κ₁ ++ Δ₁))
    SR = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ Δ₁)

    SRᶜ : Split x Θ (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δ₁) ((Μ ++ Δ ++ Κ₁) ++ Δ₁)
    SRᶜ = split-++ˡ SR₁ Δ₁

    eL : sub-sp S (sub-sp (split-++ˡ s₁' Δ₁) (t ∷ ts) g) h ≡ sp-cast qL (ihL ∷ ts)
    eL = ap (λ v → sub-sp S (sub-cons v t ts g) h) (split-++-ˡ s₁' Δ₁)
       ∙ ap (λ ρ → sub-sp S (sp-cast ρ W) h) (∙-idr flL)
       ∙ sym (λ i → sub-sp (co-ʳʳˡ Θ Γ s₂' Δ₁ i) (sp-cast-filler flL W i) h)
       ∙ ap (λ v → sub-cons v W₁ ts h) (split-++-ˡ S₀ Δ₁)
       ∙ sp-cast-∙idr qL (ihL ∷ ts)

    eR : sub-sp SR (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ˡ s₂' Δ₁)) (t ∷ ts) h) g
       ≡ sub-sp SR (sp-cast pR V) g
    eR = ap (λ s → sub-sp SR (sub-sp s (t ∷ ts) h) g) (split-behind-++ˡ s₁' s₂' Δ₁)
       ∙ ap (λ v → sub-sp SR (sub-cons v t ts h) g) (split-++-ˡ SB Δ₁)
       ∙ ap (λ ρ → sub-sp SR (sp-cast ρ V) g) (∙-idr pR)

    eV : sub-sp SRᶜ V g ≡ sp-cast qR (ihR ∷ ts)
    eV = ap (λ v → sub-cons v (sub SB t h) ts g) (split-++-ˡ SR₁ Δ₁)
       ∙ sp-cast-∙idr qR (ihR ∷ ts)

    π' : PathP (λ i → Sp (Θ ++ Γ ++ flΜ i) (A ∷ As))
           (sub-sp SRᶜ V g) (sub-sp SR (sp-cast pR V) g)
    π' i = sub-sp (co-hereˡ Θ x Μ Δ Κ₁ Δ₁ i) (sp-cast-filler pR V i) g

    seg₁ : PathP (λ i → SpΩ ((sym qL ∙ ap (_++ Δ₁) bdΚ) i))
             (sp-cast qL (ihL ∷ ts)) (ihR ∷ ts)
    seg₁ = _∙P_ {B = SpΩ} {p = sym qL} {q = ap (_++ Δ₁) bdΚ}
             (symP (sp-cast-filler qL (ihL ∷ ts)))
             (λ i → ih i ∷ ts)

    seg₂ : PathP (λ i → SpΩ (((sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR) i))
             (sp-cast qL (ihL ∷ ts)) (sub-sp SRᶜ V g)
    seg₂ = _∙P_ {B = SpΩ} {p = sym qL ∙ ap (_++ Δ₁) bdΚ} {q = qR}
             seg₁ (sp-cast-filler qR (ihR ∷ ts))
           ▷ sym eV

    seg₃ : PathP (λ i → SpΩ ((((sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flΜ) i))
             (sp-cast qL (ihL ∷ ts)) (sub-sp SR (sp-cast pR V) g)
    seg₃ = _∙P_ {B = SpΩ} {p = (sym qL ∙ ap (_++ Δ₁) bdΚ) ∙ qR}
             {q = ap (λ l → Θ ++ Γ ++ l) flΜ}
             seg₂ π'
core-cons-LR {x = x} {y = y} {A = A} {As = As} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Κ = Κ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Ξ₁ = Ξ₁} s₁' s₂' t ts g h =
  sp-over (sq-LR Θ Γ Ξ₁ Μ₂ Δ Κ) (e₁ ◁ seg₃)
  where
    SpΩ : Ctx → Type _
    SpΩ Ω = Sp Ω (A ∷ As)

    flΔ : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ₁)
    flΔ = flattenˡ Θ Γ Ξ₁ Δ₁

    flΜ₂ : (Θ ++ Γ ++ Ξ₁) ++ Μ₂ ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂)
    flΜ₂ = flattenˡ Θ Γ Ξ₁ Μ₂

    flʳΞ : Ξ₁ ++ (Μ₂ ++ Δ ++ Κ) ≡ (Ξ₁ ++ Μ₂) ++ Δ ++ Κ
    flʳΞ = flattenʳ Ξ₁ Μ₂ Δ Κ

    qL : (Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ) ≡ ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ++ Δ ++ Κ
    qL = flattenʳ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κ

    qR : (Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ) ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂ ++ Δ ++ Κ)
    qR = flattenˡ Θ Γ Ξ₁ (Μ₂ ++ Δ ++ Κ)

    pRc : Γ₁ ++ (Μ₂ ++ Δ ++ Κ) ≡ (Γ₁ ++ Μ₂) ++ Δ ++ Κ
    pRc = flattenʳ Γ₁ Μ₂ Δ Κ

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Μ₂)) (Θ ++ Γ ++ (Ξ₁ ++ Δ₁)) Κ
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂'))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) Κ
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂'

    W₁ : Tm (Θ ++ Γ ++ Ξ₁) (base A)
    W₁ = sub s₁' t g

    W : Sp ((Θ ++ Γ ++ Ξ₁) ++ Δ₁) (A ∷ As)
    W = W₁ ∷ ts

    X₂ : Sp (Μ₂ ++ Δ ++ Κ) As
    X₂ = sub-sp s₂' ts h

    X : Sp ((Θ ++ Γ ++ Ξ₁) ++ (Μ₂ ++ Δ ++ Κ)) (A ∷ As)
    X = W₁ ∷ X₂

    V : Sp (Γ₁ ++ (Μ₂ ++ Δ ++ Κ)) (A ∷ As)
    V = t ∷ X₂

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Μ₂)) ++ Δ ++ Κ) ((Ξ₁ ++ Μ₂) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κ)

    SR₀ : Split x Θ ((Γ₁ ++ Μ₂) ++ Δ ++ Κ) ((Ξ₁ ++ Μ₂) ++ Δ ++ Κ)
    SR₀ = split-++ˡ (split-++ˡ s₁' Μ₂) (Δ ++ Κ)

    SRᶜ : Split x Θ (Γ₁ ++ (Μ₂ ++ Δ ++ Κ)) (Ξ₁ ++ (Μ₂ ++ Δ ++ Κ))
    SRᶜ = split-++ˡ s₁' (Μ₂ ++ Δ ++ Κ)

    e₁ : sub-sp S (sub-sp (split-++ˡ s₁' Δ₁) (t ∷ ts) g) h ≡ sub-sp S (sp-cast flΔ W) h
    e₁ = ap (λ v → sub-sp S (sub-cons v t ts g) h) (split-++-ˡ s₁' Δ₁)
       ∙ ap (λ ρ → sub-sp S (sp-cast ρ W) h) (∙-idr flΔ)

    ℓ₂ : PathP (λ i → Sp (flΜ₂ i ++ Δ ++ Κ) (A ∷ As))
           (sub-sp Sᶜ W h) (sub-sp S (sp-cast flΔ W) h)
    ℓ₂ i = sub-sp (co-crossˡ Θ Γ Ξ₁ s₂' i) (sp-cast-filler flΔ W i) h

    e₂ : sub-sp Sᶜ W h ≡ sp-cast qL X
    e₂ = ap (λ v → sub-cons v W₁ ts h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂')
       ∙ sp-cast-∙idr qL X

    e₃ : sub-sp SR₀ (sub-sp (split-++ʳ Γ₁ s₂') (t ∷ ts) h) g ≡ sub-sp SR₀ (sp-cast pRc V) g
    e₃ = ap (λ v → sub-sp SR₀ (sub-cons v t ts h) g) (split-++-ʳ Γ₁ s₂')
       ∙ ap (λ ρ → sub-sp SR₀ (sp-cast ρ V) g) (∙-idr pRc)

    e₄ : sub-sp SRᶜ V g ≡ sp-cast qR X
    e₄ = ap (λ v → sub-cons v t X₂ g) (split-++-ˡ s₁' (Μ₂ ++ Δ ++ Κ))
       ∙ sp-cast-∙idr qR X

    π' : PathP (λ i → Sp (Θ ++ Γ ++ flʳΞ i) (A ∷ As))
           (sub-sp SRᶜ V g) (sub-sp SR₀ (sp-cast pRc V) g)
    π' i = sub-sp (co-crossʳ s₁' Μ₂ Δ Κ i) (sp-cast-filler pRc V i) g

    e₅ : sub-sp SR₀ (sub-sp (split-++ʳ Γ₁ s₂') (t ∷ ts) h) g
       ≡ sub-sp SR (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) (t ∷ ts) h) g
    e₅ j = sub-sp (co-crossʰ s₁' Μ₂ (Δ ++ Κ) j)
                  (sub-sp (split-behind-cross s₁' s₂' j) (t ∷ ts) h) g

    seg₁ : PathP (λ i → SpΩ ((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) i))
             (sub-sp S (sp-cast flΔ W) h) X
    seg₁ = _∙P_ {B = SpΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ₂)} {q = sym qL}
             (symP ℓ₂ ▷ e₂) (symP (sp-cast-filler qL X))

    seg₂ : PathP (λ i → SpΩ (((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR) i))
             (sub-sp S (sp-cast flΔ W) h) (sub-sp SRᶜ V g)
    seg₂ = _∙P_ {B = SpΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL} {q = qR}
             seg₁ (sp-cast-filler qR X)
           ▷ sym e₄

    seg₃ : PathP (λ i → SpΩ ((((sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flʳΞ) i))
             (sub-sp S (sp-cast flΔ W) h)
             (sub-sp SR (sub-sp (split-behind (split-++ˡ s₁' Δ₁) (split-++ʳ Ξ₁ s₂')) (t ∷ ts) h) g)
    seg₃ = _∙P_ {B = SpΩ} {p = (sym (ap (_++ Δ ++ Κ) flΜ₂) ∙ sym qL) ∙ qR}
             {q = ap (λ l → Θ ++ Γ ++ l) flʳΞ}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-cons-RR {x = x} {y = y} {A = A} {As = As} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ξ = Ξ} {Κ = Κ} {Γ₁ = Γ₁} {Δ₁ = Δ₁} s₁' s₂ t ts g h =
  sp-over (sq-RR Γ₁ Θ₂ Γ Μ Δ Κ) (e₁ ◁ seg₃)
  where
    SpΩ : Ctx → Type _
    SpΩ Ω = Sp Ω (A ∷ As)

    bdΘ : (Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdΘ = interchangeₘ-boundary Θ₂ Γ Μ Δ Κ

    pL : Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
    pL = flattenʳ Γ₁ Θ₂ Γ Ξ

    flΜ : Γ₁ ++ (Θ₂ ++ Γ ++ Μ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Μ
    flΜ = flattenʳ Γ₁ Θ₂ Γ Μ

    qL : Γ₁ ++ ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ) ≡ (Γ₁ ++ (Θ₂ ++ Γ ++ Μ)) ++ Δ ++ Κ
    qL = flattenʳ Γ₁ (Θ₂ ++ Γ ++ Μ) Δ Κ

    qR : Γ₁ ++ (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ (Μ ++ Δ ++ Κ)
    qR = flattenʳ Γ₁ Θ₂ Γ (Μ ++ Δ ++ Κ)

    pR : Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ) ≡ (Γ₁ ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ Κ
    pR = flattenʳ Γ₁ (Θ₂ ++ x ∷ Μ) Δ Κ

    S : Split y ((Γ₁ ++ Θ₂) ++ Γ ++ Μ) ((Γ₁ ++ Θ₂) ++ Γ ++ Ξ) Κ
    S = split-++ʳ (Γ₁ ++ Θ₂) (split-++ʳ Γ s₂)

    S₀ : Split y (Θ₂ ++ Γ ++ Μ) (Θ₂ ++ Γ ++ Ξ) Κ
    S₀ = split-++ʳ Θ₂ (split-++ʳ Γ s₂)

    Sᶜ : Split y (Γ₁ ++ (Θ₂ ++ Γ ++ Μ)) (Γ₁ ++ (Θ₂ ++ Γ ++ Ξ)) Κ
    Sᶜ = split-++ʳ Γ₁ S₀

    W₂ : Sp (Θ₂ ++ Γ ++ Ξ) As
    W₂ = sub-sp s₁' ts g

    W : Sp (Γ₁ ++ (Θ₂ ++ Γ ++ Ξ)) (A ∷ As)
    W = t ∷ W₂

    ihL : Sp ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ) As
    ihL = sub-sp S₀ W₂ h

    SB : Split y (Θ₂ ++ x ∷ Μ) Δ₁ Κ
    SB = split-behind s₁' s₂

    SR₁ : Split x Θ₂ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR₁ = split-++ˡ (split-here Θ₂ x Μ) (Δ ++ Κ)

    ihR : Sp (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ)) As
    ihR = sub-sp SR₁ (sub-sp SB ts h) g

    ih : PathP (λ i → Sp (bdΘ i) As) ihL ihR
    ih = sub-sp-interchange s₁' s₂ ts g h

    V : Sp (Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ)) (A ∷ As)
    V = t ∷ sub-sp SB ts h

    SR : Split x (Γ₁ ++ Θ₂) (((Γ₁ ++ Θ₂) ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γ₁ ++ Θ₂) x Μ) (Δ ++ Κ)

    SR' : Split x (Γ₁ ++ Θ₂) ((Γ₁ ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR' = split-++ˡ (split-++ʳ Γ₁ (split-here Θ₂ x Μ)) (Δ ++ Κ)

    SRᶜ : Split x (Γ₁ ++ Θ₂) (Γ₁ ++ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ)) (Μ ++ Δ ++ Κ)
    SRᶜ = split-++ʳ Γ₁ SR₁

    e₁ : sub-sp S (sub-sp (split-++ʳ Γ₁ s₁') (t ∷ ts) g) h ≡ sub-sp S (sp-cast pL W) h
    e₁ = ap (λ v → sub-sp S (sub-cons v t ts g) h) (split-++-ʳ Γ₁ s₁')
       ∙ ap (λ ρ → sub-sp S (sp-cast ρ W) h) (∙-idr pL)

    ℓ₂ : PathP (λ i → Sp (flΜ i ++ Δ ++ Κ) (A ∷ As))
           (sub-sp Sᶜ W h) (sub-sp S (sp-cast pL W) h)
    ℓ₂ i = sub-sp (co-ʳʳʳ Γ₁ Θ₂ Γ s₂ i) (sp-cast-filler pL W i) h

    e₂ : sub-sp Sᶜ W h ≡ sp-cast qL (t ∷ ihL)
    e₂ = ap (λ v → sub-cons v t W₂ h) (split-++-ʳ Γ₁ S₀)
       ∙ sp-cast-∙idr qL (t ∷ ihL)

    eV : sub-sp SRᶜ V g ≡ sp-cast qR (t ∷ ihR)
    eV = ap (λ v → sub-cons v t (sub-sp SB ts h) g) (split-++-ʳ Γ₁ SR₁)
       ∙ sp-cast-∙idr qR (t ∷ ihR)

    π' : sub-sp SRᶜ V g ≡ sub-sp SR' (sp-cast pR V) g
    π' i = sub-sp (co-hereʳ Γ₁ Θ₂ x Μ Δ Κ i) (sp-cast-filler pR V i) g

    eR : sub-sp SR (sub-sp (split-behind (split-++ʳ Γ₁ s₁') s₂) (t ∷ ts) h) g
       ≡ sub-sp SR' (sp-cast pR V) g
    eR = (λ j → sub-sp (split-++ˡ (symP (split-here-++ʳ Γ₁ Θ₂ x Μ) j) (Δ ++ Κ))
                       (sub-sp (split-behind-++ʳ Γ₁ s₁' s₂ j) (t ∷ ts) h) g)
       ∙ ap (λ v → sub-sp SR' (sub-cons v t ts h) g) (split-++-ʳ Γ₁ SB)
       ∙ ap (λ ρ → sub-sp SR' (sp-cast ρ V) g) (∙-idr pR)

    seg₁ : PathP (λ i → SpΩ ((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL) i))
             (sub-sp S (sp-cast pL W) h) (t ∷ ihL)
    seg₁ = _∙P_ {B = SpΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ)} {q = sym qL}
             (symP ℓ₂ ▷ e₂) (symP (sp-cast-filler qL (t ∷ ihL)))

    seg₂ : PathP (λ i → SpΩ (((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                              ∙ ap (Γ₁ ++_) bdΘ) i))
             (sub-sp S (sp-cast pL W) h) (t ∷ ihR)
    seg₂ = _∙P_ {B = SpΩ} {p = sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL}
             {q = ap (Γ₁ ++_) bdΘ}
             seg₁ (λ i → t ∷ ih i)

    seg₃ : PathP (λ i → SpΩ ((((sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                               ∙ ap (Γ₁ ++_) bdΘ) ∙ qR) i))
             (sub-sp S (sp-cast pL W) h)
             (sub-sp SR (sub-sp (split-behind (split-++ʳ Γ₁ s₁') s₂) (t ∷ ts) h) g)
    seg₃ = _∙P_ {B = SpΩ} {p = (sym (ap (_++ Δ ++ Κ) flΜ) ∙ sym qL)
                               ∙ ap (Γ₁ ++_) bdΘ} {q = qR}
             seg₂ (sp-cast-filler qR (t ∷ ihR))
           ▷ (sym eV ∙ π' ∙ sym eR)
core-m⊗-ΓΓ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁' s₂' P Q g h =
  tm-over (sq-LL Θ Γ Μ Δ Κ₁ (Ψ ++ Δm)) (eLt ◁ segO₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βΔ : Ctx
    βΔ = A ∷ B ∷ Δm

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    bdΚ : (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΚ = interchangeₘ-boundary Θ Γ Μ Δ Κ₁

    bdβ : (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ) ≡ Θ ++ Γ ++ (Μ ++ Δ ++ (Κ₁ ++ βΔ))
    bdβ = interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ βΔ)

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flᵦL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ βΔ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ)
    flᵦL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ βΔ

    flᵦR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ βΔ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ βΔ)
    flᵦR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) βΔ

    flᵦʳ : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ βΔ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ βΔ)
    flᵦʳ = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ βΔ

    flΜβ : (Μ ++ Δ ++ Κ₁) ++ βΔ ≡ Μ ++ Δ ++ (Κ₁ ++ βΔ)
    flΜβ = flattenˡ Μ Δ Κ₁ βΔ

    flΜΨ : (Μ ++ Δ ++ Κ₁) ++ ΨΔ ≡ Μ ++ Δ ++ (Κ₁ ++ ΨΔ)
    flΜΨ = flattenˡ Μ Δ Κ₁ ΨΔ

    qL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ ΨΔ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)
    qL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ ΨΔ

    qR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ ΨΔ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ ΨΔ)
    qR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) ΨΔ

    pRm : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)
    pRm = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ ΨΔ

    S : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) (Κ₁ ++ ΨΔ)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' ΨΔ))

    S₀ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ Ξ₁) Κ₁
    S₀ = split-++ʳ Θ (split-++ʳ Γ s₂')

    Sᵦᶜ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) (Κ₁ ++ βΔ)
    Sᵦᶜ = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' βΔ))

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    π-in : sub Sᵦᶜ QgRaw h ≡ sub (split-++ˡ S₀ βΔ) Qg h
    π-in i = sub (symP (co-ʳʳˡ Θ Γ s₂' βΔ) i) (cast-filler (sym flᵦ) QgRaw i) h

    ihLt : Tm ((Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ)) C
    ihLt = sub Sᵦᶜ QgRaw h

    uLc : Tm (((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ βΔ) C
    uLc = cast (sym flᵦL) ihLt

    SB : Split y (Θ ++ x ∷ Μ) Γm Κ₁
    SB = split-behind s₁' s₂'

    QhRaw : Tm ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ βΔ)) C
    QhRaw = sub (split-++ˡ SB βΔ) Q h

    Qh' : Tm (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ βΔ) C
    Qh' = cast (sym flᵦʳ) QhRaw

    SR₁ : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁)

    ihRt' : Tm (Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ βΔ)) C
    ihRt' = sub (split-++ˡ SR₁ βΔ) Qh' g

    uRc : Tm ((Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ βΔ) C
    uRc = cast (sym flᵦR) ihRt'

    ih : PathP (λ i → Tm (bdβ i) C)
           ihLt
           (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ))
                (sub (split-behind (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ)) Q h) g)
    ih = sub-interchange (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ) Q g h

    ehᵦ : sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ))
              (sub (split-behind (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ)) Q h) g
        ≡ sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g
    ehᵦ = ap (λ s → sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) (sub s Q h) g)
             (split-behind-++ˡ s₁' s₂' βΔ)

    π-innR : PathP (λ i → Tm (Θ ++ Γ ++ sym flΜβ i) C)
               (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g)
               ihRt'
    π-innR i = sub (symP (co-hereˡ Θ x Μ Δ Κ₁ βΔ) i)
                   (cast-filler (sym flᵦʳ) QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL ∙ bdβ) i)) uLc
           (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g)
    M₁ = _∙P_ {B = TmC} {p = flᵦL} {q = bdβ}
           (symP (cast-filler (sym flᵦL) ihLt)) (ih ▷ ehᵦ)

    M₂ : PathP (λ i → TmC (((flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)) i))
           uLc ihRt'
    M₂ = _∙P_ {B = TmC} {p = flᵦL ∙ bdβ} {q = ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)}
           M₁ π-innR

    M₃ : PathP (λ i → TmC ((((flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ))
                            ∙ sym flᵦR) i))
           uLc uRc
    M₃ = _∙P_ {B = TmC} {p = (flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)}
           {q = sym flᵦR}
           M₂ (cast-filler (sym flᵦR) ihRt')

    M : PathP (λ j → TmC (ap (_++ βΔ) bdΚ j)) uLc uRc
    M = tm-over (sq-LL-inv Θ Γ Μ Δ Κ₁ βΔ) M₃

    WL : Tm (((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) C
    WL = match⊗ {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P uLc

    WR' : Tm ((Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ ΨΔ) C
    WR' = match⊗ {Γ = Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)} {Δ = Δm} P uRc

    Wc : PathP (λ j → TmC (ap (_++ ΨΔ) bdΚ j)) WL WR'
    Wc j = match⊗ {Γ = bdΚ j} {Δ = Δm} P (M j)

    WR : Tm (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) C
    WR = match⊗ {Γ = (Θ ++ x ∷ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P Qh'

    SRᶜm : Split x Θ (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) ((Μ ++ Δ ++ Κ₁) ++ ΨΔ)
    SRᶜm = split-++ˡ SR₁ ΨΔ

    SR : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)) (Μ ++ Δ ++ (Κ₁ ++ ΨΔ))
    SR = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ ΨΔ)

    eLt : sub S (sub (split-++ˡ s₁' ΨΔ) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h
        ≡ cast qL WL
    eLt = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
        ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)
        ∙ sym (λ i → sub (co-ʳʳˡ Θ Γ s₂' ΨΔ i) (cast-filler flΨΔ W i) h)
        ∙ ap (λ v → sub-match⊗ˡ v P Qg h) (split-++-ˡ S₀ ΨΔ)
        ∙ cast-∙idr qL (match⊗ {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P
            (cast (sym flᵦL) (sub (split-++ˡ S₀ βΔ) Qg h)))
        ∙ ap (λ u → cast qL (match⊗ {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P
                              (cast (sym flᵦL) u)))
             (sym π-in)

    eV : sub SRᶜm WR g ≡ cast qR WR'
    eV = ap (λ v → sub-match⊗ˡ v P Qh' g) (split-++-ˡ SR₁ ΨΔ)
       ∙ cast-∙idr qR WR'

    π'R : PathP (λ i → Tm (Θ ++ Γ ++ flΜΨ i) C)
            (sub SRᶜm WR g) (sub SR (cast pRm WR) g)
    π'R i = sub (co-hereˡ Θ x Μ Δ Κ₁ ΨΔ i) (cast-filler pRm WR i) g

    eRt : sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ˡ s₂' ΨΔ))
                      (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g
        ≡ sub SR (cast pRm WR) g
    eRt = ap (λ s → sub SR (sub s (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)
             (split-behind-++ˡ s₁' s₂' ΨΔ)
        ∙ ap (λ v → sub SR (sub-match⊗ˡ v P Q h) g) (split-++-ˡ SB ΨΔ)
        ∙ ap (λ ρ → sub SR (cast ρ WR) g) (∙-idr pRm)

    segO₁ : PathP (λ i → TmC ((sym qL ∙ ap (_++ ΨΔ) bdΚ) i)) (cast qL WL) WR'
    segO₁ = _∙P_ {B = TmC} {p = sym qL} {q = ap (_++ ΨΔ) bdΚ}
              (symP (cast-filler qL WL)) Wc

    segO₂ : PathP (λ i → TmC (((sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR) i))
              (cast qL WL) (sub SRᶜm WR g)
    segO₂ = _∙P_ {B = TmC} {p = sym qL ∙ ap (_++ ΨΔ) bdΚ} {q = qR}
              segO₁ (cast-filler qR WR')
            ▷ sym eV

    segO₃ : PathP (λ i → TmC ((((sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR)
                               ∙ ap (λ l → Θ ++ Γ ++ l) flΜΨ) i))
              (cast qL WL)
              (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ˡ s₂' ΨΔ))
                           (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)
    segO₃ = _∙P_ {B = TmC} {p = (sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR}
              {q = ap (λ l → Θ ++ Γ ++ l) flΜΨ}
              segO₂ π'R
            ▷ sym eRt
core-m⊗-ΓΨ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Κᵧ = Κᵧ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁' s₂ᵧ P Q g h =
  tm-over (sq-ΓΨ Θ Γ Ξ₁ Μ₂ Δ Κᵧ Δm) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = A ⊗ B

    βΔ : Ctx
    βΔ = A ∷ B ∷ Δm

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match⊗ {Γ = Γm} {Δ = Δm} P Q

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flΜ₂ : (Θ ++ Γ ++ Ξ₁) ++ Μ₂ ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂)
    flΜ₂ = flattenˡ Θ Γ Ξ₁ Μ₂

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flᵐΞ : Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm ≡ (Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    flᵐΞ = flattenᵐ Ξ₁ Μ₂ Δ Κᵧ Δm

    qLᵐ : (Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
        ≡ ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    qLᵐ = flattenᵐ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κᵧ Δm

    qR : (Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
       ≡ Θ ++ Γ ++ (Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
    qR = flattenˡ Θ Γ Ξ₁ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)

    pRᵐ : Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm) ≡ (Γm ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    pRᵐ = flattenᵐ Γm Μ₂ Δ Κᵧ Δm

    s₂ᶜ : Split y Μ₂ (Ψ ++ Δm) (Κᵧ ++ Δm)
    s₂ᶜ = split-++ˡ s₂ᵧ Δm

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Μ₂)) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) (Κᵧ ++ Δm)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᶜ))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) (Κᵧ ++ Δm)
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂ᶜ

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    Ph : Tm (Μ₂ ++ Δ ++ Κᵧ) AB
    Ph = sub s₂ᵧ P h

    X : Tm ((Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) C
    X = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} Ph Qg

    WRi : Tm (Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) C
    WRi = match⊗ {Γ = Γm} {Δ = Δm} Ph Q

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Μ₂)) ++ Δ ++ (Κᵧ ++ Δm))
                 ((Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm))
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κᵧ ++ Δm)

    SR₀ : Split x Θ ((Γm ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)) ((Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm))
    SR₀ = split-++ˡ (split-++ˡ s₁' Μ₂) (Δ ++ Κᵧ ++ Δm)

    SRᶜ : Split x Θ (Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) (Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
    SRᶜ = split-++ˡ s₁' ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)

    e₁ : sub S (sub (split-++ˡ s₁' ΨΔ) T g) h ≡ sub S (cast flΨΔ W) h
    e₁ = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)

    ℓ₂ : PathP (λ i → Tm (flΜ₂ i ++ Δ ++ (Κᵧ ++ Δm)) C)
           (sub Sᶜ W h) (sub S (cast flΨΔ W) h)
    ℓ₂ i = sub (co-crossˡ Θ Γ Ξ₁ s₂ᶜ i) (cast-filler flΨΔ W i) h

    e₂ : sub Sᶜ W h ≡ cast qLᵐ X
    e₂ = ap (λ v → sub-match⊗ˡ v P Qg h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂ᶜ)
       ∙ ap (λ v → sub-match⊗ʳ v refl P Qg h) (split-++-ˡ s₂ᵧ Δm)
       ∙ cast-∙idr qLᵐ X

    e₄ : sub SRᶜ WRi g ≡ cast qR X
    e₄ = ap (λ v → sub-match⊗ˡ v Ph Q g) (split-++-ˡ s₁' ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm))
       ∙ cast-∙idr qR X

    π' : PathP (λ i → Tm (Θ ++ Γ ++ flᵐΞ i) C)
           (sub SRᶜ WRi g) (sub SR₀ (cast pRᵐ WRi) g)
    π' i = sub (co-crossᵐ s₁' Μ₂ Δ Κᵧ Δm i) (cast-filler pRᵐ WRi i) g

    e₃ : sub SR₀ (sub (split-++ʳ Γm s₂ᶜ) T h) g ≡ sub SR₀ (cast pRᵐ WRi) g
    e₃ = ap (λ v → sub SR₀ (sub-match⊗ˡ v P Q h) g) (split-++-ʳ Γm s₂ᶜ)
       ∙ ap (λ v → sub SR₀ (sub-match⊗ʳ v refl P Q h) g) (split-++-ˡ s₂ᵧ Δm)
       ∙ ap (λ ρ → sub SR₀ (cast ρ WRi) g) (∙-idr pRᵐ)

    e₅ : sub SR₀ (sub (split-++ʳ Γm s₂ᶜ) T h) g
       ≡ sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂ᶜ)) T h) g
    e₅ j = sub (co-crossʰ s₁' Μ₂ (Δ ++ Κᵧ ++ Δm) j)
               (sub (split-behind-cross s₁' s₂ᶜ j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) i))
             (sub S (cast flΨΔ W) h) X
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂)} {q = sym qLᵐ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵐ X))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR) i))
             (sub S (cast flΨΔ W) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ} {q = qR}
             seg₁ (cast-filler qR X)
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flᵐΞ) i))
             (sub S (cast flΨΔ W) h)
             (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂ᶜ)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR)}
             {q = ap (λ l → Θ ++ Γ ++ l) flᵐΞ}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-m⊗-ΓΔ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ = Θ} {Γ = Γ} {Μᵧ = Μᵧ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁' s₂ᵧ P Q g h =
  tm-over (sq-ΓΔ-outer Θ Γ Ξ₁ Ψ Μᵧ Δ Κ) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βΔ : Ctx
    βΔ = A ∷ B ∷ Δm

    βΜ : Ctx
    βΜ = A ∷ B ∷ Μᵧ

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    wrapβ : ∀ {y' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split y' Θ' Λ Ξ' → Split y' (A ∷ B ∷ Θ') (A ∷ B ∷ Λ) Ξ'
    wrapβ = split-++ʳ (A ∷ B ∷ [])

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match⊗ {Γ = Γm} {Δ = Δm} P Q

    s₂c : Split y (Ψ ++ Μᵧ) (Ψ ++ Δm) Κ
    s₂c = split-++ʳ Ψ s₂ᵧ

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flΨΜ : (Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ) ≡ Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ)
    flΨΜ = flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ)

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flβΜ : (Θ ++ Γ ++ Ξ₁) ++ βΜ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΜ)
    flβΜ = flattenˡ Θ Γ Ξ₁ βΜ

    flᵦL' : (Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ) ≡ ((Θ ++ Γ ++ Ξ₁) ++ βΜ) ++ Δ ++ Κ
    flᵦL' = flattenʳ (Θ ++ Γ ++ Ξ₁) βΜ Δ Κ

    flᵦʳ : Γm ++ (βΜ ++ Δ ++ Κ) ≡ (Γm ++ βΜ) ++ Δ ++ Κ
    flᵦʳ = flattenʳ Γm βΜ Δ Κ

    flʳΞᵦ : Ξ₁ ++ (βΜ ++ Δ ++ Κ) ≡ (Ξ₁ ++ βΜ) ++ Δ ++ Κ
    flʳΞᵦ = flattenʳ Ξ₁ βΜ Δ Κ

    flᵦR' : (Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ) ≡ Θ ++ Γ ++ (Ξ₁ ++ βΜ ++ Δ ++ Κ)
    flᵦR' = flattenˡ Θ Γ Ξ₁ (βΜ ++ Δ ++ Κ)

    qLᵇ : (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)
        ≡ ((Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    qLᵇ = bury (Θ ++ Γ ++ Ξ₁) Ψ Μᵧ (Δ ++ Κ)

    qR : (Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)
       ≡ Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ ++ Δ ++ Κ)
    qR = flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ ++ Δ ++ Κ)

    pRᵇ : Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    pRᵇ = bury Γm Ψ Μᵧ (Δ ++ Κ)

    bdᵦ : (Θ ++ Γ ++ (Ξ₁ ++ βΜ)) ++ Δ ++ Κ ≡ Θ ++ Γ ++ ((Ξ₁ ++ βΜ) ++ Δ ++ Κ)
    bdᵦ = interchangeₘ-boundary Θ Γ (Ξ₁ ++ βΜ) Δ Κ

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ)) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) Κ
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂c))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ)) ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) Κ
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂c

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    QhRaw : Tm ((Γm ++ βΜ) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ s₂ᵧ)) Q h

    Qh' : Tm (Γm ++ (βΜ ++ Δ ++ Κ)) C
    Qh' = cast (sym flᵦʳ) QhRaw

    innerL : Tm (((Θ ++ Γ ++ Ξ₁) ++ βΜ) ++ Δ ++ Κ) C
    innerL = sub (split-++ʳ (Θ ++ Γ ++ Ξ₁) (wrapβ s₂ᵧ)) Qg h

    uL' : Tm ((Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ)) C
    uL' = cast (sym flᵦL') innerL

    WL : Tm ((Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WL = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P uL'

    innerR : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΜ ++ Δ ++ Κ)) C
    innerR = sub (split-++ˡ s₁' (βΜ ++ Δ ++ Κ)) Qh' g

    uR' : Tm ((Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ)) C
    uR' = cast (sym flᵦR') innerR

    WR' : Tm ((Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WR' = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P uR'

    WRi : Tm (Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WRi = match⊗ {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} P Qh'

    s₂ⁱ : Split y (Ξ₁ ++ βΜ) (Ξ₁ ++ βΔ) Κ
    s₂ⁱ = split-++ʳ Ξ₁ (wrapβ s₂ᵧ)

    ihL : Tm ((Θ ++ Γ ++ (Ξ₁ ++ βΜ)) ++ Δ ++ Κ) C
    ihL = sub (split-++ʳ Θ (split-++ʳ Γ s₂ⁱ)) QgRaw h

    ihR : Tm (Θ ++ Γ ++ ((Ξ₁ ++ βΜ) ++ Δ ++ Κ)) C
    ihR = sub (split-++ˡ (split-here Θ x (Ξ₁ ++ βΜ)) (Δ ++ Κ))
              (sub (split-behind (split-++ˡ s₁' βΔ) s₂ⁱ) Q h) g

    ih : PathP (λ i → Tm (bdᵦ i) C) ihL ihR
    ih = sub-interchange (split-++ˡ s₁' βΔ) s₂ⁱ Q g h

    π-in : PathP (λ i → Tm (flβΜ i ++ Δ ++ Κ) C) innerL ihL
    π-in i = sub (co-crossˡ Θ Γ Ξ₁ (wrapβ s₂ᵧ) i)
                 (symP (cast-filler (sym flᵦ) QgRaw) i) h

    e₆ : sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g ≡ ihR
    e₆ j = sub (co-crossʰ s₁' βΜ (Δ ++ Κ) j)
               (sub (split-behind-cross s₁' (wrapβ s₂ᵧ) j) Q h) g

    π-innR : PathP (λ i → Tm (Θ ++ Γ ++ sym flʳΞᵦ i) C)
               (sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g) innerR
    π-innR i = sub (symP (co-crossʳ s₁' βΜ Δ Κ) i)
                   (cast-filler (sym flᵦʳ) QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) i)) uL' ihL
    M₁ = _∙P_ {B = TmC} {p = flᵦL'} {q = ap (_++ Δ ++ Κ) flβΜ}
           (symP (cast-filler (sym flᵦL') innerL)) π-in

    M₂ : PathP (λ i → TmC (((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ) i))
           uL' (sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g)
    M₂ = _∙P_ {B = TmC} {p = flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ} {q = bdᵦ}
           M₁ (ih ▷ sym e₆)

    M₃ : PathP (λ i → TmC ((((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                            ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)) i))
           uL' innerR
    M₃ = _∙P_ {B = TmC} {p = (flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ}
           {q = ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)}
           M₂ π-innR

    M₄ : PathP (λ i → TmC (((((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                             ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)) ∙ sym flᵦR') i))
           uL' uR'
    M₄ = _∙P_ {B = TmC} {p = ((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                             ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)} {q = sym flᵦR'}
           M₃ (cast-filler (sym flᵦR') innerR)

    M : uL' ≡ uR'
    M = tm-over (sq-ΓΔ-inner Θ Γ Ξ₁ βΜ Δ Κ) M₄

    Wc : WL ≡ WR'
    Wc j = match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P (M j)

    SRᶜ : Split x Θ (Γm ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)) (Ξ₁ ++ Ψ ++ Μᵧ ++ Δ ++ Κ)
    SRᶜ = split-++ˡ s₁' (Ψ ++ Μᵧ ++ Δ ++ Κ)

    SR₀ : Split x Θ ((Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ) ((Ξ₁ ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ)
    SR₀ = split-++ˡ (split-++ˡ s₁' (Ψ ++ Μᵧ)) (Δ ++ Κ)

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Ψ ++ Μᵧ)) ++ Δ ++ Κ)
                 ((Ξ₁ ++ Ψ ++ Μᵧ) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Ψ ++ Μᵧ)) (Δ ++ Κ)

    e₁ : sub S (sub (split-++ˡ s₁' ΨΔ) T g) h ≡ sub S (cast flΨΔ W) h
    e₁ = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)

    ℓ₂ : PathP (λ i → Tm (flΨΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ W h) (sub S (cast flΨΔ W) h)
    ℓ₂ i = sub (co-crossˡ Θ Γ Ξ₁ s₂c i) (cast-filler flΨΔ W i) h

    e₂ : sub Sᶜ W h ≡ cast qLᵇ WL
    e₂ = ap (λ v → sub-match⊗ˡ v P Qg h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂c)
       ∙ ap (λ v → sub-match⊗ʳ v refl P Qg h) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) WL)
            (∙-idr (refl {x = (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ Μᵧ}))
       ∙ cast-∙idr qLᵇ WL

    e₄ : sub SRᶜ WRi g ≡ cast qR WR'
    e₄ = ap (λ v → sub-match⊗ˡ v P Qh' g) (split-++-ˡ s₁' (Ψ ++ Μᵧ ++ Δ ++ Κ))
       ∙ cast-∙idr qR WR'

    π' : PathP (λ i → Tm (Θ ++ Γ ++ bury Ξ₁ Ψ Μᵧ (Δ ++ Κ) i) C)
           (sub SRᶜ WRi g) (sub SR₀ (cast pRᵇ WRi) g)
    π' i = sub (co-crossᵇ s₁' Ψ Μᵧ (Δ ++ Κ) i) (cast-filler pRᵇ WRi i) g

    e₃ : sub SR₀ (sub (split-++ʳ Γm s₂c) T h) g ≡ sub SR₀ (cast pRᵇ WRi) g
    e₃ = ap (λ v → sub SR₀ (sub-match⊗ˡ v P Q h) g) (split-++-ʳ Γm s₂c)
       ∙ ap (λ v → sub SR₀ (sub-match⊗ʳ v refl P Q h) g) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → sub SR₀ (cast (pRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRi) g)
            (∙-idr (refl {x = Γm ++ Ψ ++ Μᵧ}))
       ∙ ap (λ ρ → sub SR₀ (cast ρ WRi) g) (∙-idr pRᵇ)

    e₅ : sub SR₀ (sub (split-++ʳ Γm s₂c) T h) g
       ≡ sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂c)) T h) g
    e₅ j = sub (co-crossʰ s₁' (Ψ ++ Μᵧ) (Δ ++ Κ) j)
               (sub (split-behind-cross s₁' s₂c j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) i))
             (sub S (cast flΨΔ W) h) WL
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flΨΜ)} {q = sym qLᵇ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ WL))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR) i))
             (sub S (cast flΨΔ W) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ} {q = qR}
             (seg₁ ▷ Wc) (cast-filler qR WR')
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) (bury Ξ₁ Ψ Μᵧ (Δ ++ Κ))) i))
             (sub S (cast flΨΔ W) h)
             (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂c)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR)}
             {q = ap (λ l → Θ ++ Γ ++ l) (bury Ξ₁ Ψ Μᵧ (Δ ++ Κ))}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-m⊗-ΨΨ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁'' s₂'' P Q g h =
  tm-over (sq-ΨΨ Γm Θ₂ Γ Μ Δ Κ₁ Δm) (e₁ ◁ seg₄)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = A ⊗ B

    bdΘ₂ : (Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΘ₂ = interchangeₘ-boundary Θ₂ Γ Μ Δ Κ₁

    flᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)
    flᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm

    flʳΜ : Γm ++ (Θ₂ ++ Γ ++ Μ) ≡ (Γm ++ Θ₂) ++ Γ ++ Μ
    flʳΜ = flattenʳ Γm Θ₂ Γ Μ

    qLᵐ : Γm ++ (((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ Δm)
        ≡ (Γm ++ (Θ₂ ++ Γ ++ Μ)) ++ Δ ++ (Κ₁ ++ Δm)
    qLᵐ = flattenᵐ Γm (Θ₂ ++ Γ ++ Μ) Δ Κ₁ Δm

    qRᵐ : Γm ++ ((Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ Δm)
        ≡ (Γm ++ Θ₂) ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ Δm)
    qRᵐ = flattenᵐ Γm Θ₂ Γ (Μ ++ Δ ++ Κ₁) Δm

    pRᵐ : Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm)
        ≡ (Γm ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ (Κ₁ ++ Δm)
    pRᵐ = flattenᵐ Γm (Θ₂ ++ x ∷ Μ) Δ Κ₁ Δm

    flΜΔm : (Μ ++ Δ ++ Κ₁) ++ Δm ≡ Μ ++ Δ ++ (Κ₁ ++ Δm)
    flΜΔm = flattenˡ Μ Δ Κ₁ Δm

    s₂ᶜ : Split y Μ (Ξ₁ ++ Δm) (Κ₁ ++ Δm)
    s₂ᶜ = split-++ˡ s₂'' Δm

    S : Split y ((Γm ++ Θ₂) ++ Γ ++ Μ) ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)) (Κ₁ ++ Δm)
    S = split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ s₂ᶜ)

    S₀' : Split y (Θ₂ ++ Γ ++ Μ) (Θ₂ ++ Γ ++ Ξ₁) Κ₁
    S₀' = split-++ʳ Θ₂ (split-++ʳ Γ s₂'')

    Sᵐ : Split y (Θ₂ ++ Γ ++ Μ) ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) (Κ₁ ++ Δm)
    Sᵐ = split-++ˡ S₀' Δm

    Sᶜ : Split y (Γm ++ (Θ₂ ++ Γ ++ Μ)) (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) (Κ₁ ++ Δm)
    Sᶜ = split-++ʳ Γm Sᵐ

    Wg : Tm (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) C
    Wg = match⊗ {Γ = Γm} {Δ = Δm} (sub s₁'' P g) Q

    ihL : Tm ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁) AB
    ihL = sub S₀' (sub s₁'' P g) h

    SB : Split y (Θ₂ ++ x ∷ Μ) Ψ Κ₁
    SB = split-behind s₁'' s₂''

    SR₁ : Split x Θ₂ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ₂ x Μ) (Δ ++ Κ₁)

    ihR : Tm (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) AB
    ihR = sub SR₁ (sub SB P h) g

    ih : PathP (λ i → Tm (bdΘ₂ i) AB) ihL ihR
    ih = sub-interchange s₁'' s₂'' P g h

    WRᵇ : Tm (Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm)) C
    WRᵇ = match⊗ {Γ = Γm} {Δ = Δm} (sub SB P h) Q

    SRᵐ : Split x Θ₂ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm) ((Μ ++ Δ ++ Κ₁) ++ Δm)
    SRᵐ = split-++ˡ SR₁ Δm

    SRᶜ : Split x (Γm ++ Θ₂) (Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm))
                  ((Μ ++ Δ ++ Κ₁) ++ Δm)
    SRᶜ = split-++ʳ Γm SRᵐ

    SRb : Split x (Γm ++ Θ₂) ((Γm ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ (Κ₁ ++ Δm))
                  (Μ ++ Δ ++ (Κ₁ ++ Δm))
    SRb = split-++ˡ (split-++ʳ Γm (split-here Θ₂ x Μ)) (Δ ++ Κ₁ ++ Δm)

    SR : Split x (Γm ++ Θ₂) (((Γm ++ Θ₂) ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δm))
                 (Μ ++ Δ ++ (Κ₁ ++ Δm))
    SR = split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ₁ ++ Δm)

    e₁ : sub S (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᵐ Wg) h
    e₁ = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁'' Δm))
       ∙ ap (λ v → sub S (sub-match⊗ʳ v refl P Q g) h) (split-++-ˡ s₁'' Δm)
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr flᵐ)

    ℓ₂ : PathP (λ i → Tm (flʳΜ i ++ Δ ++ (Κ₁ ++ Δm)) C)
           (sub Sᶜ Wg h) (sub S (cast flᵐ Wg) h)
    ℓ₂ i = sub (co-mid Γm Θ₂ Γ s₂'' Δm i) (cast-filler flᵐ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)
    e₂ = ap (λ v → sub-match⊗ˡ v (sub s₁'' P g) Q h) (split-++-ʳ Γm Sᵐ)
       ∙ ap (λ v → sub-match⊗ʳ v refl (sub s₁'' P g) Q h) (split-++-ˡ S₀' Δm)
       ∙ cast-∙idr qLᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)

    eV : sub SRᶜ WRᵇ g ≡ cast qRᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihR Q)
    eV = ap (λ v → sub-match⊗ˡ v (sub SB P h) Q g) (split-++-ʳ Γm SRᵐ)
       ∙ ap (λ v → sub-match⊗ʳ v refl (sub SB P h) Q g) (split-++-ˡ SR₁ Δm)
       ∙ cast-∙idr qRᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihR Q)

    π'R : PathP (λ i → Tm ((Γm ++ Θ₂) ++ Γ ++ flΜΔm i) C)
            (sub SRᶜ WRᵇ g) (sub SRb (cast pRᵐ WRᵇ) g)
    π'R i = sub (co-midʰ Γm Θ₂ x Μ Δ Κ₁ Δm i) (cast-filler pRᵐ WRᵇ i) g

    eR : sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) s₂ᶜ)
                     (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g
       ≡ sub SRb (cast pRᵐ WRᵇ) g
    eR = (λ j → sub (split-++ˡ (symP (split-here-++ʳ Γm Θ₂ x Μ) j) (Δ ++ Κ₁ ++ Δm))
                    (sub (split-behind-++ʳ Γm (split-++ˡ s₁'' Δm) s₂ᶜ j)
                         (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)
       ∙ ap (λ s → sub SRb (sub (split-++ʳ Γm s) (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)
            (split-behind-++ˡ s₁'' s₂'' Δm)
       ∙ ap (λ v → sub SRb (sub-match⊗ˡ v P Q h) g)
            (split-++-ʳ Γm (split-++ˡ SB Δm))
       ∙ ap (λ v → sub SRb (sub-match⊗ʳ v refl P Q h) g) (split-++-ˡ SB Δm)
       ∙ ap (λ ρ → sub SRb (cast ρ WRᵇ) g) (∙-idr pRᵐ)

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ) i))
             (sub S (cast flᵐ Wg) h) (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ)} {q = sym qLᵐ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                              ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) i))
             (sub S (cast flᵐ Wg) h) (match⊗ {Γ = Γm} {Δ = Δm} ihR Q)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ}
             {q = ap (λ l → Γm ++ l ++ Δm) bdΘ₂}
             seg₁ (λ j → match⊗ {Γ = Γm} {Δ = Δm} (ih j) Q)

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                               ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ) i))
             (sub S (cast flᵐ Wg) h) (sub SRᶜ WRᵇ g)
    seg₃ = _∙P_ {B = TmC} {p = (sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                               ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂} {q = qRᵐ}
             seg₂ (cast-filler qRᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihR Q))
           ▷ sym eV

    seg₄ : PathP (λ i → TmC (((((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                                ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ)
                              ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flΜΔm) i))
             (sub S (cast flᵐ Wg) h)
             (sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) s₂ᶜ)
                          (match⊗ {Γ = Γm} {Δ = Δm} P Q) h) g)
    seg₄ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                                ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ}
             {q = ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flΜΔm}
             seg₃ π'R
           ▷ sym eR
core-m⊗-ΨΔ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μᵧ = Μᵧ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁'' s₂ᵧ P Q g h =
  tm-over (sq-ΨΔ Γm Θ₂ Γ Ξ₁ Μᵧ Δ Κ) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = A ⊗ B

    βΜ : Ctx
    βΜ = A ∷ B ∷ Μᵧ

    wrapβ : ∀ {y' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split y' Θ' Λ Ξ' → Split y' (A ∷ B ∷ Θ') (A ∷ B ∷ Λ) Ξ'
    wrapβ = split-++ʳ (A ∷ B ∷ [])

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match⊗ {Γ = Γm} {Δ = Δm} P Q

    flᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)
    flᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm

    flᵐΜ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ)
    flᵐΜ = flattenᵐ Γm Θ₂ Γ Ξ₁ Μᵧ

    qLᵇ : Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ)
        ≡ (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ)) ++ Δ ++ Κ
    qLᵇ = bury Γm (Θ₂ ++ Γ ++ Ξ₁) Μᵧ (Δ ++ Κ)

    qRᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ))
        ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ ++ Δ ++ Κ)
    qRᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ (Μᵧ ++ Δ ++ Κ)

    pRᵇ : Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    pRᵇ = bury Γm Ψ Μᵧ (Δ ++ Κ)

    flᵦʳ : Γm ++ (βΜ ++ Δ ++ Κ) ≡ (Γm ++ βΜ) ++ Δ ++ Κ
    flᵦʳ = flattenʳ Γm βΜ Δ Κ

    flʳΞΜ : Ξ₁ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Ξ₁ ++ Μᵧ) ++ Δ ++ Κ
    flʳΞΜ = flattenʳ Ξ₁ Μᵧ Δ Κ

    Pg : Tm (Θ₂ ++ Γ ++ Ξ₁) AB
    Pg = sub s₁'' P g

    Wg : Tm (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) C
    Wg = match⊗ {Γ = Γm} {Δ = Δm} Pg Q

    QhRaw : Tm ((Γm ++ βΜ) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ s₂ᵧ)) Q h

    Qh' : Tm (Γm ++ (βΜ ++ Δ ++ Κ)) C
    Qh' = cast (sym flᵦʳ) QhRaw

    X : Tm (Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ)) C
    X = match⊗ {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} Pg Qh'

    WRi : Tm (Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WRi = match⊗ {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} P Qh'

    S : Split y ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ)) ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)) Κ
    S = split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᵧ))

    Sᶜ : Split y (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ)) (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) Κ
    Sᶜ = split-++ʳ Γm (split-++ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ)

    SRᶜ : Split x (Γm ++ Θ₂) (Γm ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)) (Ξ₁ ++ Μᵧ ++ Δ ++ Κ)
    SRᶜ = split-++ʳ Γm (split-++ˡ s₁'' (Μᵧ ++ Δ ++ Κ))

    SRb₀ : Split x (Γm ++ Θ₂) ((Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ) ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SRb₀ = split-++ˡ (split-++ʳ Γm (split-++ˡ s₁'' Μᵧ)) (Δ ++ Κ)

    SRb₁ : Split x (Γm ++ Θ₂) ((Γm ++ (Θ₂ ++ x ∷ (Ξ₁ ++ Μᵧ))) ++ Δ ++ Κ)
                   ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SRb₁ = split-++ˡ (split-++ʳ Γm (split-here Θ₂ x (Ξ₁ ++ Μᵧ))) (Δ ++ Κ)

    SR : Split x (Γm ++ Θ₂) (((Γm ++ Θ₂) ++ x ∷ (Ξ₁ ++ Μᵧ)) ++ Δ ++ Κ)
                 ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γm ++ Θ₂) x (Ξ₁ ++ Μᵧ)) (Δ ++ Κ)

    e₁ : sub S (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) T g) h ≡ sub S (cast flᵐ Wg) h
    e₁ = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁'' Δm))
       ∙ ap (λ v → sub S (sub-match⊗ʳ v refl P Q g) h) (split-++-ˡ s₁'' Δm)
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr flᵐ)

    ℓ₂ : PathP (λ i → Tm (flᵐΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ Wg h) (sub S (cast flᵐ Wg) h)
    ℓ₂ i = sub (co-midᵧ Γm Θ₂ Γ Ξ₁ s₂ᵧ i) (cast-filler flᵐ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵇ X
    e₂ = ap (λ v → sub-match⊗ˡ v Pg Q h) (split-++-ʳ Γm (split-++ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ))
       ∙ ap (λ v → sub-match⊗ʳ v refl Pg Q h) (split-++-ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ)
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) X)
            (∙-idr (refl {x = Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ}))
       ∙ cast-∙idr qLᵇ X

    e₄ : sub SRᶜ WRi g ≡ cast qRᵐ X
    e₄ = ap (λ v → sub-match⊗ˡ v P Qh' g) (split-++-ʳ Γm (split-++ˡ s₁'' (Μᵧ ++ Δ ++ Κ)))
       ∙ ap (λ v → sub-match⊗ʳ v refl P Qh' g) (split-++-ˡ s₁'' (Μᵧ ++ Δ ++ Κ))
       ∙ cast-∙idr qRᵐ X

    π' : PathP (λ i → Tm ((Γm ++ Θ₂) ++ Γ ++ flʳΞΜ i) C)
           (sub SRᶜ WRi g) (sub SRb₀ (cast pRᵇ WRi) g)
    π' i = sub (co-midᵇ Γm s₁'' Μᵧ Δ Κ i) (cast-filler pRᵇ WRi i) g

    e₃ : sub SRb₀ (sub (split-++ʳ Γm (split-++ʳ Ψ s₂ᵧ)) T h) g
       ≡ sub SRb₀ (cast pRᵇ WRi) g
    e₃ = ap (λ v → sub SRb₀ (sub-match⊗ˡ v P Q h) g) (split-++-ʳ Γm (split-++ʳ Ψ s₂ᵧ))
       ∙ ap (λ v → sub SRb₀ (sub-match⊗ʳ v refl P Q h) g) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → sub SRb₀ (cast (pRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRi) g)
            (∙-idr (refl {x = Γm ++ Ψ ++ Μᵧ}))
       ∙ ap (λ ρ → sub SRb₀ (cast ρ WRi) g) (∙-idr pRᵇ)

    c₂ : sub SRb₀ (sub (split-++ʳ Γm (split-++ʳ Ψ s₂ᵧ)) T h) g
       ≡ sub SRb₁ (sub (split-++ʳ Γm (split-behind (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ))) T h) g
    c₂ j = sub (split-++ˡ (split-++ʳ Γm (co-crossᵖ s₁'' Μᵧ j)) (Δ ++ Κ))
               (sub (split-++ʳ Γm (split-behind-cross s₁'' s₂ᵧ j)) T h) g

    c₁ : sub SRb₁ (sub (split-++ʳ Γm (split-behind (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ))) T h) g
       ≡ sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ)) T h) g
    c₁ j = sub (split-++ˡ (split-here-++ʳ Γm Θ₂ x (Ξ₁ ++ Μᵧ) j) (Δ ++ Κ))
               (sub (symP (split-behind-++ʳ Γm (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ)) j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) i))
             (sub S (cast flᵐ Wg) h) X
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flᵐΜ)} {q = sym qLᵇ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ X))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ) i))
             (sub S (cast flᵐ Wg) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ} {q = qRᵐ}
             seg₁ (cast-filler qRᵐ X)
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ)
                              ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flʳΞΜ) i))
             (sub S (cast flᵐ Wg) h)
             (sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ)}
             {q = ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flʳΞΜ}
             seg₂ π'
           ▷ (sym e₃ ∙ c₂ ∙ c₁)
core-m⊗-ΔΔ {x = x} {y = y} {A = A} {B = B} {C = C} {Θ₃ = Θ₃} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ξ = Ξ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} s₁'' s₂ P Q g h =
  tm-over (sq-ΔΔ-outer Γm Ψ Θ₃ Γ Μ Δ Κ) (e₁ ◁ segO₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βctx : Ctx → Ctx
    βctx l = A ∷ B ∷ l

    wrapβ : ∀ {x' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split x' Θ' Λ Ξ' → Split x' (βctx Θ') (βctx Λ) Ξ'
    wrapβ = split-++ʳ (A ∷ B ∷ [])

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match⊗ {Γ = Γm} {Δ = Δm} P Q

    bdΘ₃ : (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdΘ₃ = interchangeₘ-boundary Θ₃ Γ Μ Δ Κ

    bdᵦ : ((Γm ++ βctx Θ₃) ++ Γ ++ Μ) ++ Δ ++ Κ
        ≡ (Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdᵦ = interchangeₘ-boundary (Γm ++ βctx Θ₃) Γ Μ Δ Κ

    buryΞ : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ Ξ
    buryΞ = bury Γm Ψ Θ₃ (Γ ++ Ξ)

    buryΜ : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ Μ
    buryΜ = bury Γm Ψ Θ₃ (Γ ++ Μ)

    qLᵇ : Γm ++ Ψ ++ ((Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)
        ≡ (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ
    qLᵇ = bury Γm Ψ (Θ₃ ++ Γ ++ Μ) (Δ ++ Κ)

    qRᵇ : Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)
        ≡ (Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ
    qRᵇ = bury Γm Ψ (Θ₃ ++ x ∷ Μ) (Δ ++ Κ)

    qRc : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))
        ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    qRc = bury Γm Ψ Θ₃ (Γ ++ Μ ++ Δ ++ Κ)

    flᵦˡ : Γm ++ βctx (Θ₃ ++ Γ ++ Ξ) ≡ (Γm ++ βctx Θ₃) ++ Γ ++ Ξ
    flᵦˡ = flattenʳ Γm (βctx Θ₃) Γ Ξ

    flᵦΜ : Γm ++ βctx (Θ₃ ++ Γ ++ Μ) ≡ (Γm ++ βctx Θ₃) ++ Γ ++ Μ
    flᵦΜ = flattenʳ Γm (βctx Θ₃) Γ Μ

    flᵦL' : Γm ++ (βctx (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)
          ≡ (Γm ++ βctx (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ
    flᵦL' = flattenʳ Γm (βctx (Θ₃ ++ Γ ++ Μ)) Δ Κ

    flᵦʳ' : Γm ++ (βctx (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)
          ≡ (Γm ++ βctx (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ
    flᵦʳ' = flattenʳ Γm (βctx (Θ₃ ++ x ∷ Μ)) Δ Κ

    flᵦR' : Γm ++ βctx (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))
          ≡ (Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    flᵦR' = flattenʳ Γm (βctx Θ₃) Γ (Μ ++ Δ ++ Κ)

    s₁ᶜ : Split x (Γm ++ Ψ ++ Θ₃) (Γm ++ Ψ ++ Δm) Ξ
    s₁ᶜ = split-++ʳ Γm (split-++ʳ Ψ s₁'')

    S : Split y ((Γm ++ Ψ ++ Θ₃) ++ Γ ++ Μ) ((Γm ++ Ψ ++ Θ₃) ++ Γ ++ Ξ) Κ
    S = split-++ʳ (Γm ++ Ψ ++ Θ₃) (split-++ʳ Γ s₂)

    S₂' : Split y (Θ₃ ++ Γ ++ Μ) (Θ₃ ++ Γ ++ Ξ) Κ
    S₂' = split-++ʳ Θ₃ (split-++ʳ Γ s₂)

    Sᶜ : Split y (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)) (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ)) Κ
    Sᶜ = split-++ʳ Γm (split-++ʳ Ψ S₂')

    QgRaw : Tm ((Γm ++ βctx Θ₃) ++ Γ ++ Ξ) C
    QgRaw = sub (split-++ʳ Γm (wrapβ s₁'')) Q g

    Qg : Tm (Γm ++ βctx (Θ₃ ++ Γ ++ Ξ)) C
    Qg = cast (sym flᵦˡ) QgRaw

    Wg : Tm (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ)) C
    Wg = match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P Qg

    innerL : Tm ((Γm ++ βctx (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ) C
    innerL = sub (split-++ʳ Γm (wrapβ S₂')) Qg h

    uL : Tm (Γm ++ (βctx (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)) C
    uL = cast (sym flᵦL') innerL

    WLᵇ : Tm (Γm ++ Ψ ++ ((Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)) C
    WLᵇ = match⊗ {Γ = Γm} {Δ = (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ} P uL

    SBh : Split y (Θ₃ ++ x ∷ Μ) Δm Κ
    SBh = split-behind s₁'' s₂

    QhRaw : Tm ((Γm ++ βctx (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ SBh)) Q h

    sᵦ : Split x (βctx Θ₃) (βctx (Θ₃ ++ x ∷ Μ)) Μ
    sᵦ = split-++ʳ (A ∷ B ∷ []) (split-here Θ₃ x Μ)

    SR₃ : Split x Θ₃ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR₃ = split-++ˡ (split-here Θ₃ x Μ) (Δ ++ Κ)

    SRᵦ' : Split x (Γm ++ βctx Θ₃) (Γm ++ (βctx (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ))
                   (Μ ++ Δ ++ Κ)
    SRᵦ' = split-++ʳ Γm (wrapβ SR₃)

    innerR : Tm ((Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)) C
    innerR = sub SRᵦ' (cast (sym flᵦʳ') QhRaw) g

    uR : Tm (Γm ++ βctx (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))) C
    uR = cast (sym flᵦR') innerR

    WRᵇ' : Tm (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))) C
    WRᵇ' = match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ)} P uR

    ihLt : Tm (((Γm ++ βctx Θ₃) ++ Γ ++ Μ) ++ Δ ++ Κ) C
    ihLt = sub (split-++ʳ (Γm ++ βctx Θ₃) (split-++ʳ Γ s₂)) QgRaw h

    ih : PathP (λ i → Tm (bdᵦ i) C)
           ihLt
           (sub (split-++ˡ (split-here (Γm ++ βctx Θ₃) x Μ) (Δ ++ Κ))
                (sub (split-behind (split-++ʳ Γm (wrapβ s₁'')) s₂) Q h) g)
    ih = sub-interchange (split-++ʳ Γm (wrapβ s₁'')) s₂ Q g h

    π-in : PathP (λ i → Tm (flᵦΜ i ++ Δ ++ Κ) C) innerL ihLt
    π-in i = sub (co-ʳʳʳ Γm (βctx Θ₃) Γ s₂ i)
                 (symP (cast-filler (sym flᵦˡ) QgRaw) i) h

    b₁ : sub (split-++ˡ (split-here (Γm ++ βctx Θ₃) x Μ) (Δ ++ Κ))
             (sub (split-behind (split-++ʳ Γm (wrapβ s₁'')) s₂) Q h) g
       ≡ sub (split-++ˡ (split-++ʳ Γm (split-here (βctx Θ₃) x Μ)) (Δ ++ Κ))
             (sub (split-++ʳ Γm (split-behind (wrapβ s₁'') s₂)) Q h) g
    b₁ j = sub (split-++ˡ (symP (split-here-++ʳ Γm (βctx Θ₃) x Μ) j) (Δ ++ Κ))
               (sub (split-behind-++ʳ Γm (wrapβ s₁'') s₂ j) Q h) g

    b₂ : sub (split-++ˡ (split-++ʳ Γm (split-here (βctx Θ₃) x Μ)) (Δ ++ Κ))
             (sub (split-++ʳ Γm (split-behind (wrapβ s₁'') s₂)) Q h) g
       ≡ sub (split-++ˡ (split-++ʳ Γm sᵦ) (Δ ++ Κ)) QhRaw g
    b₂ j = sub (split-++ˡ (split-++ʳ Γm (symP (split-here-++ʳ (A ∷ B ∷ []) Θ₃ x Μ) j))
                          (Δ ++ Κ))
               (sub (split-++ʳ Γm (split-behind-++ʳ (A ∷ B ∷ []) s₁'' s₂ j)) Q h) g

    π-innR : sub (split-++ˡ (split-++ʳ Γm sᵦ) (Δ ++ Κ)) QhRaw g ≡ innerR
    π-innR i = sub (symP (co-flʳˡ Γm sᵦ Δ Κ) i)
                   (cast-filler (sym flᵦʳ') QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) i)) uL ihLt
    M₁ = _∙P_ {B = TmC} {p = flᵦL'} {q = ap (_++ Δ ++ Κ) flᵦΜ}
           (symP (cast-filler (sym flᵦL') innerL)) π-in

    M₂ : PathP (λ i → TmC (((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ) i)) uL innerR
    M₂ = _∙P_ {B = TmC} {p = flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ} {q = bdᵦ}
           M₁ (ih ▷ (b₁ ∙ b₂ ∙ π-innR))

    M₃ : PathP (λ i → TmC ((((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ) ∙ sym flᵦR') i))
           uL uR
    M₃ = _∙P_ {B = TmC} {p = (flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ} {q = sym flᵦR'}
           M₂ (cast-filler (sym flᵦR') innerR)

    sq-inner : ∀ (Γ₁ : Ctx)
      → ((flattenʳ Γ₁ (βctx (Θ₃ ++ Γ ++ Μ)) Δ Κ
          ∙ ap (_++ Δ ++ Κ) (flattenʳ Γ₁ (βctx Θ₃) Γ Μ))
         ∙ interchangeₘ-boundary (Γ₁ ++ βctx Θ₃) Γ Μ Δ Κ)
        ∙ sym (flattenʳ Γ₁ (βctx Θ₃) Γ (Μ ++ Δ ++ Κ))
      ≡ ap (λ l → Γ₁ ++ βctx l) (interchangeₘ-boundary Θ₃ Γ Μ Δ Κ)
    sq-inner Γ₁ = list!

    M : PathP (λ j → TmC (ap (λ l → Γm ++ βctx l) bdΘ₃ j)) uL uR
    M = tm-over (sq-inner Γm) M₃

    Wc : PathP (λ j → TmC (Γm ++ Ψ ++ bdΘ₃ j)) WLᵇ WRᵇ'
    Wc j = match⊗ {Γ = Γm} {Δ = bdΘ₃ j} P (M j)

    WRb : Tm (Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)) C
    WRb = match⊗ {Γ = Γm} {Δ = (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ} P (cast (sym flᵦʳ') QhRaw)

    SRᶜb : Split x (Γm ++ Ψ ++ Θ₃) (Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ))
                   (Μ ++ Δ ++ Κ)
    SRᶜb = split-++ʳ Γm (split-++ʳ Ψ SR₃)

    SRb : Split x (Γm ++ Ψ ++ Θ₃) ((Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ)
                  (Μ ++ Δ ++ Κ)
    SRb = split-++ˡ (split-++ʳ Γm (split-++ʳ Ψ (split-here Θ₃ x Μ))) (Δ ++ Κ)

    SR : Split x (Γm ++ Ψ ++ Θ₃) (((Γm ++ Ψ ++ Θ₃) ++ x ∷ Μ) ++ Δ ++ Κ)
                 (Μ ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γm ++ Ψ ++ Θ₃) x Μ) (Δ ++ Κ)

    e₁ : sub S (sub s₁ᶜ T g) h ≡ sub S (cast buryΞ Wg) h
    e₁ = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ʳ Γm (split-++ʳ Ψ s₁''))
       ∙ ap (λ v → sub S (sub-match⊗ʳ v refl P Q g) h) (split-++-ʳ Ψ s₁'')
       ∙ ap (λ ρ → sub S (cast (buryΞ ∙ ap (_++ Γ ++ Ξ) ρ) Wg) h) (∙-idr (refl {x = Γm ++ Ψ ++ Θ₃}))
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr buryΞ)

    ℓ₂ : PathP (λ i → Tm (buryΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ Wg h) (sub S (cast buryΞ Wg) h)
    ℓ₂ i = sub (co-bury Γm Ψ Θ₃ Γ s₂ i) (cast-filler buryΞ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵇ WLᵇ
    e₂ = ap (λ v → sub-match⊗ˡ v P Qg h) (split-++-ʳ Γm (split-++ʳ Ψ S₂'))
       ∙ ap (λ v → sub-match⊗ʳ v refl P Qg h) (split-++-ʳ Ψ S₂')
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) WLᵇ) (∙-idr (refl {x = Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)}))
       ∙ cast-∙idr qLᵇ WLᵇ

    eV : sub SRᶜb WRb g ≡ cast qRc WRᵇ'
    eV = ap (λ v → sub-match⊗ˡ v P (cast (sym flᵦʳ') QhRaw) g)
            (split-++-ʳ Γm (split-++ʳ Ψ SR₃))
       ∙ ap (λ v → sub-match⊗ʳ v refl P (cast (sym flᵦʳ') QhRaw) g)
            (split-++-ʳ Ψ SR₃)
       ∙ ap (λ ρ → cast (qRc ∙ ap (_++ Γ ++ Μ ++ Δ ++ Κ) ρ) WRᵇ') (∙-idr (refl {x = Γm ++ Ψ ++ Θ₃}))
       ∙ cast-∙idr qRc WRᵇ'

    π'R : sub SRᶜb WRb g ≡ sub SRb (cast qRᵇ WRb) g
    π'R i = sub (co-buryʰ Γm Ψ Θ₃ x Μ (Δ ++ Κ) i) (cast-filler qRᵇ WRb i) g

    eR : sub SR (sub (split-behind s₁ᶜ s₂) T h) g ≡ sub SRb (cast qRᵇ WRb) g
    eR = (λ j → sub (split-++ˡ (symP (split-here-++ʳ Γm (Ψ ++ Θ₃) x Μ) j) (Δ ++ Κ))
                    (sub (split-behind-++ʳ Γm (split-++ʳ Ψ s₁'') s₂ j) T h) g)
       ∙ (λ j → sub (split-++ˡ (split-++ʳ Γm (symP (split-here-++ʳ Ψ Θ₃ x Μ) j))
                               (Δ ++ Κ))
                    (sub (split-++ʳ Γm (split-behind-++ʳ Ψ s₁'' s₂ j)) T h) g)
       ∙ ap (λ v → sub SRb (sub-match⊗ˡ v P Q h) g)
            (split-++-ʳ Γm (split-++ʳ Ψ SBh))
       ∙ ap (λ v → sub SRb (sub-match⊗ʳ v refl P Q h) g) (split-++-ʳ Ψ SBh)
       ∙ ap (λ ρ → sub SRb (cast (qRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRb) g) (∙-idr (refl {x = Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)}))
       ∙ ap (λ ρ → sub SRb (cast ρ WRb) g) (∙-idr qRᵇ)

    segO₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ) i))
              (sub S (cast buryΞ Wg) h) WLᵇ
    segO₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) buryΜ)} {q = sym qLᵇ}
              (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ WLᵇ))

    segO₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                               ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃) i))
              (sub S (cast buryΞ Wg) h) WRᵇ'
    segO₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ}
              {q = ap (λ l → Γm ++ Ψ ++ l) bdΘ₃}
              segO₁ Wc

    segO₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                                ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃) ∙ qRc) i))
              (sub S (cast buryΞ Wg) h)
              (sub SR (sub (split-behind s₁ᶜ s₂) T h) g)
    segO₃ = _∙P_ {B = TmC} {p = (sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                                ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃} {q = qRc}
              segO₂ (cast-filler qRc WRᵇ')
            ▷ (sym eV ∙ π'R ∙ sym eR)
core-m𝟙-ΓΓ {x = x} {y = y} {C = C} {Θ = Θ} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁' s₂' P Q g h =
  tm-over (sq-LL Θ Γ Μ Δ Κ₁ (Ψ ++ Δm)) (eLt ◁ segO₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βΔ : Ctx
    βΔ = Δm

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    bdΚ : (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΚ = interchangeₘ-boundary Θ Γ Μ Δ Κ₁

    bdβ : (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ) ≡ Θ ++ Γ ++ (Μ ++ Δ ++ (Κ₁ ++ βΔ))
    bdβ = interchangeₘ-boundary Θ Γ Μ Δ (Κ₁ ++ βΔ)

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flᵦL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ βΔ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ)
    flᵦL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ βΔ

    flᵦR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ βΔ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ βΔ)
    flᵦR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) βΔ

    flᵦʳ : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ βΔ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ βΔ)
    flᵦʳ = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ βΔ

    flΜβ : (Μ ++ Δ ++ Κ₁) ++ βΔ ≡ Μ ++ Δ ++ (Κ₁ ++ βΔ)
    flΜβ = flattenˡ Μ Δ Κ₁ βΔ

    flΜΨ : (Μ ++ Δ ++ Κ₁) ++ ΨΔ ≡ Μ ++ Δ ++ (Κ₁ ++ ΨΔ)
    flΜΨ = flattenˡ Μ Δ Κ₁ ΨΔ

    qL : ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ ΨΔ ≡ (Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)
    qL = flattenˡ (Θ ++ Γ ++ Μ) Δ Κ₁ ΨΔ

    qR : (Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ ΨΔ ≡ Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ ΨΔ)
    qR = flattenˡ Θ Γ (Μ ++ Δ ++ Κ₁) ΨΔ

    pRm : ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ ≡ (Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)
    pRm = flattenˡ (Θ ++ x ∷ Μ) Δ Κ₁ ΨΔ

    S : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) (Κ₁ ++ ΨΔ)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' ΨΔ))

    S₀ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ Ξ₁) Κ₁
    S₀ = split-++ʳ Θ (split-++ʳ Γ s₂')

    Sᵦᶜ : Split y (Θ ++ Γ ++ Μ) (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) (Κ₁ ++ βΔ)
    Sᵦᶜ = split-++ʳ Θ (split-++ʳ Γ (split-++ˡ s₂' βΔ))

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    π-in : sub Sᵦᶜ QgRaw h ≡ sub (split-++ˡ S₀ βΔ) Qg h
    π-in i = sub (symP (co-ʳʳˡ Θ Γ s₂' βΔ) i) (cast-filler (sym flᵦ) QgRaw i) h

    ihLt : Tm ((Θ ++ Γ ++ Μ) ++ Δ ++ (Κ₁ ++ βΔ)) C
    ihLt = sub Sᵦᶜ QgRaw h

    uLc : Tm (((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ βΔ) C
    uLc = cast (sym flᵦL) ihLt

    SB : Split y (Θ ++ x ∷ Μ) Γm Κ₁
    SB = split-behind s₁' s₂'

    QhRaw : Tm ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ βΔ)) C
    QhRaw = sub (split-++ˡ SB βΔ) Q h

    Qh' : Tm (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ βΔ) C
    Qh' = cast (sym flᵦʳ) QhRaw

    SR₁ : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁)

    ihRt' : Tm (Θ ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ βΔ)) C
    ihRt' = sub (split-++ˡ SR₁ βΔ) Qh' g

    uRc : Tm ((Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ βΔ) C
    uRc = cast (sym flᵦR) ihRt'

    ih : PathP (λ i → Tm (bdβ i) C)
           ihLt
           (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ))
                (sub (split-behind (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ)) Q h) g)
    ih = sub-interchange (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ) Q g h

    ehᵦ : sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ))
              (sub (split-behind (split-++ˡ s₁' βΔ) (split-++ˡ s₂' βΔ)) Q h) g
        ≡ sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g
    ehᵦ = ap (λ s → sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) (sub s Q h) g)
             (split-behind-++ˡ s₁' s₂' βΔ)

    π-innR : PathP (λ i → Tm (Θ ++ Γ ++ sym flΜβ i) C)
               (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g)
               ihRt'
    π-innR i = sub (symP (co-hereˡ Θ x Μ Δ Κ₁ βΔ) i)
                   (cast-filler (sym flᵦʳ) QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL ∙ bdβ) i)) uLc
           (sub (split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ βΔ)) QhRaw g)
    M₁ = _∙P_ {B = TmC} {p = flᵦL} {q = bdβ}
           (symP (cast-filler (sym flᵦL) ihLt)) (ih ▷ ehᵦ)

    M₂ : PathP (λ i → TmC (((flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)) i))
           uLc ihRt'
    M₂ = _∙P_ {B = TmC} {p = flᵦL ∙ bdβ} {q = ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)}
           M₁ π-innR

    M₃ : PathP (λ i → TmC ((((flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ))
                            ∙ sym flᵦR) i))
           uLc uRc
    M₃ = _∙P_ {B = TmC} {p = (flᵦL ∙ bdβ) ∙ ap (λ l → Θ ++ Γ ++ l) (sym flΜβ)}
           {q = sym flᵦR}
           M₂ (cast-filler (sym flᵦR) ihRt')

    M : PathP (λ j → TmC (ap (_++ βΔ) bdΚ j)) uLc uRc
    M = tm-over (sq-LL-inv Θ Γ Μ Δ Κ₁ βΔ) M₃

    WL : Tm (((Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) C
    WL = match𝟙 {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P uLc

    WR' : Tm ((Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ ΨΔ) C
    WR' = match𝟙 {Γ = Θ ++ Γ ++ (Μ ++ Δ ++ Κ₁)} {Δ = Δm} P uRc

    Wc : PathP (λ j → TmC (ap (_++ ΨΔ) bdΚ j)) WL WR'
    Wc j = match𝟙 {Γ = bdΚ j} {Δ = Δm} P (M j)

    WR : Tm (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) C
    WR = match𝟙 {Γ = (Θ ++ x ∷ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P Qh'

    SRᶜm : Split x Θ (((Θ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ ΨΔ) ((Μ ++ Δ ++ Κ₁) ++ ΨΔ)
    SRᶜm = split-++ˡ SR₁ ΨΔ

    SR : Split x Θ ((Θ ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ ΨΔ)) (Μ ++ Δ ++ (Κ₁ ++ ΨΔ))
    SR = split-++ˡ (split-here Θ x Μ) (Δ ++ Κ₁ ++ ΨΔ)

    eLt : sub S (sub (split-++ˡ s₁' ΨΔ) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h
        ≡ cast qL WL
    eLt = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
        ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)
        ∙ sym (λ i → sub (co-ʳʳˡ Θ Γ s₂' ΨΔ i) (cast-filler flΨΔ W i) h)
        ∙ ap (λ v → sub-match𝟙ˡ v P Qg h) (split-++-ˡ S₀ ΨΔ)
        ∙ cast-∙idr qL (match𝟙 {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P
            (cast (sym flᵦL) (sub (split-++ˡ S₀ βΔ) Qg h)))
        ∙ ap (λ u → cast qL (match𝟙 {Γ = (Θ ++ Γ ++ Μ) ++ Δ ++ Κ₁} {Δ = Δm} P
                              (cast (sym flᵦL) u)))
             (sym π-in)

    eV : sub SRᶜm WR g ≡ cast qR WR'
    eV = ap (λ v → sub-match𝟙ˡ v P Qh' g) (split-++-ˡ SR₁ ΨΔ)
       ∙ cast-∙idr qR WR'

    π'R : PathP (λ i → Tm (Θ ++ Γ ++ flΜΨ i) C)
            (sub SRᶜm WR g) (sub SR (cast pRm WR) g)
    π'R i = sub (co-hereˡ Θ x Μ Δ Κ₁ ΨΔ i) (cast-filler pRm WR i) g

    eRt : sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ˡ s₂' ΨΔ))
                      (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g
        ≡ sub SR (cast pRm WR) g
    eRt = ap (λ s → sub SR (sub s (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)
             (split-behind-++ˡ s₁' s₂' ΨΔ)
        ∙ ap (λ v → sub SR (sub-match𝟙ˡ v P Q h) g) (split-++-ˡ SB ΨΔ)
        ∙ ap (λ ρ → sub SR (cast ρ WR) g) (∙-idr pRm)

    segO₁ : PathP (λ i → TmC ((sym qL ∙ ap (_++ ΨΔ) bdΚ) i)) (cast qL WL) WR'
    segO₁ = _∙P_ {B = TmC} {p = sym qL} {q = ap (_++ ΨΔ) bdΚ}
              (symP (cast-filler qL WL)) Wc

    segO₂ : PathP (λ i → TmC (((sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR) i))
              (cast qL WL) (sub SRᶜm WR g)
    segO₂ = _∙P_ {B = TmC} {p = sym qL ∙ ap (_++ ΨΔ) bdΚ} {q = qR}
              segO₁ (cast-filler qR WR')
            ▷ sym eV

    segO₃ : PathP (λ i → TmC ((((sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR)
                               ∙ ap (λ l → Θ ++ Γ ++ l) flΜΨ) i))
              (cast qL WL)
              (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ˡ s₂' ΨΔ))
                           (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)
    segO₃ = _∙P_ {B = TmC} {p = (sym qL ∙ ap (_++ ΨΔ) bdΚ) ∙ qR}
              {q = ap (λ l → Θ ++ Γ ++ l) flΜΨ}
              segO₂ π'R
            ▷ sym eRt
core-m𝟙-ΓΨ {x = x} {y = y} {C = C} {Θ = Θ} {Γ = Γ} {Μ₂ = Μ₂} {Δ = Δ} {Κᵧ = Κᵧ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁' s₂ᵧ P Q g h =
  tm-over (sq-ΓΨ Θ Γ Ξ₁ Μ₂ Δ Κᵧ Δm) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = 𝟙

    βΔ : Ctx
    βΔ = Δm

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match𝟙 {Γ = Γm} {Δ = Δm} P Q

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flΜ₂ : (Θ ++ Γ ++ Ξ₁) ++ Μ₂ ≡ Θ ++ Γ ++ (Ξ₁ ++ Μ₂)
    flΜ₂ = flattenˡ Θ Γ Ξ₁ Μ₂

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flᵐΞ : Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm ≡ (Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    flᵐΞ = flattenᵐ Ξ₁ Μ₂ Δ Κᵧ Δm

    qLᵐ : (Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
        ≡ ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    qLᵐ = flattenᵐ (Θ ++ Γ ++ Ξ₁) Μ₂ Δ Κᵧ Δm

    qR : (Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
       ≡ Θ ++ Γ ++ (Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
    qR = flattenˡ Θ Γ Ξ₁ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)

    pRᵐ : Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm) ≡ (Γm ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)
    pRᵐ = flattenᵐ Γm Μ₂ Δ Κᵧ Δm

    s₂ᶜ : Split y Μ₂ (Ψ ++ Δm) (Κᵧ ++ Δm)
    s₂ᶜ = split-++ˡ s₂ᵧ Δm

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Μ₂)) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) (Κᵧ ++ Δm)
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᶜ))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ Μ₂) ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) (Κᵧ ++ Δm)
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂ᶜ

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    Ph : Tm (Μ₂ ++ Δ ++ Κᵧ) AB
    Ph = sub s₂ᵧ P h

    X : Tm ((Θ ++ Γ ++ Ξ₁) ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) C
    X = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} Ph Qg

    WRi : Tm (Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) C
    WRi = match𝟙 {Γ = Γm} {Δ = Δm} Ph Q

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Μ₂)) ++ Δ ++ (Κᵧ ++ Δm))
                 ((Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm))
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Μ₂)) (Δ ++ Κᵧ ++ Δm)

    SR₀ : Split x Θ ((Γm ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm)) ((Ξ₁ ++ Μ₂) ++ Δ ++ (Κᵧ ++ Δm))
    SR₀ = split-++ˡ (split-++ˡ s₁' Μ₂) (Δ ++ Κᵧ ++ Δm)

    SRᶜ : Split x Θ (Γm ++ ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)) (Ξ₁ ++ (Μ₂ ++ Δ ++ Κᵧ) ++ Δm)
    SRᶜ = split-++ˡ s₁' ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm)

    e₁ : sub S (sub (split-++ˡ s₁' ΨΔ) T g) h ≡ sub S (cast flΨΔ W) h
    e₁ = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)

    ℓ₂ : PathP (λ i → Tm (flΜ₂ i ++ Δ ++ (Κᵧ ++ Δm)) C)
           (sub Sᶜ W h) (sub S (cast flΨΔ W) h)
    ℓ₂ i = sub (co-crossˡ Θ Γ Ξ₁ s₂ᶜ i) (cast-filler flΨΔ W i) h

    e₂ : sub Sᶜ W h ≡ cast qLᵐ X
    e₂ = ap (λ v → sub-match𝟙ˡ v P Qg h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂ᶜ)
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Qg h) (split-++-ˡ s₂ᵧ Δm)
       ∙ cast-∙idr qLᵐ X

    e₄ : sub SRᶜ WRi g ≡ cast qR X
    e₄ = ap (λ v → sub-match𝟙ˡ v Ph Q g) (split-++-ˡ s₁' ((Μ₂ ++ Δ ++ Κᵧ) ++ Δm))
       ∙ cast-∙idr qR X

    π' : PathP (λ i → Tm (Θ ++ Γ ++ flᵐΞ i) C)
           (sub SRᶜ WRi g) (sub SR₀ (cast pRᵐ WRi) g)
    π' i = sub (co-crossᵐ s₁' Μ₂ Δ Κᵧ Δm i) (cast-filler pRᵐ WRi i) g

    e₃ : sub SR₀ (sub (split-++ʳ Γm s₂ᶜ) T h) g ≡ sub SR₀ (cast pRᵐ WRi) g
    e₃ = ap (λ v → sub SR₀ (sub-match𝟙ˡ v P Q h) g) (split-++-ʳ Γm s₂ᶜ)
       ∙ ap (λ v → sub SR₀ (sub-match𝟙ʳ v refl P Q h) g) (split-++-ˡ s₂ᵧ Δm)
       ∙ ap (λ ρ → sub SR₀ (cast ρ WRi) g) (∙-idr pRᵐ)

    e₅ : sub SR₀ (sub (split-++ʳ Γm s₂ᶜ) T h) g
       ≡ sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂ᶜ)) T h) g
    e₅ j = sub (co-crossʰ s₁' Μ₂ (Δ ++ Κᵧ ++ Δm) j)
               (sub (split-behind-cross s₁' s₂ᶜ j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) i))
             (sub S (cast flΨΔ W) h) X
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂)} {q = sym qLᵐ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵐ X))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR) i))
             (sub S (cast flΨΔ W) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ} {q = qR}
             seg₁ (cast-filler qR X)
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) flᵐΞ) i))
             (sub S (cast flΨΔ W) h)
             (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂ᶜ)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κᵧ ++ Δm) flΜ₂) ∙ sym qLᵐ) ∙ qR)}
             {q = ap (λ l → Θ ++ Γ ++ l) flᵐΞ}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-m𝟙-ΓΔ {x = x} {y = y} {C = C} {Θ = Θ} {Γ = Γ} {Μᵧ = Μᵧ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁' s₂ᵧ P Q g h =
  tm-over (sq-ΓΔ-outer Θ Γ Ξ₁ Ψ Μᵧ Δ Κ) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βΔ : Ctx
    βΔ = Δm

    βΜ : Ctx
    βΜ = Μᵧ

    ΨΔ : Ctx
    ΨΔ = Ψ ++ Δm

    wrapβ : ∀ {y' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split y' Θ' Λ Ξ' → Split y' (Θ') (Λ) Ξ'
    wrapβ = split-++ʳ ([])

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match𝟙 {Γ = Γm} {Δ = Δm} P Q

    s₂c : Split y (Ψ ++ Μᵧ) (Ψ ++ Δm) Κ
    s₂c = split-++ʳ Ψ s₂ᵧ

    flΨΔ : (Θ ++ Γ ++ Ξ₁) ++ ΨΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)
    flΨΔ = flattenˡ Θ Γ Ξ₁ ΨΔ

    flΨΜ : (Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ) ≡ Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ)
    flΨΜ = flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ)

    flᵦ : (Θ ++ Γ ++ Ξ₁) ++ βΔ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΔ)
    flᵦ = flattenˡ Θ Γ Ξ₁ βΔ

    flβΜ : (Θ ++ Γ ++ Ξ₁) ++ βΜ ≡ Θ ++ Γ ++ (Ξ₁ ++ βΜ)
    flβΜ = flattenˡ Θ Γ Ξ₁ βΜ

    flᵦL' : (Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ) ≡ ((Θ ++ Γ ++ Ξ₁) ++ βΜ) ++ Δ ++ Κ
    flᵦL' = flattenʳ (Θ ++ Γ ++ Ξ₁) βΜ Δ Κ

    flᵦʳ : Γm ++ (βΜ ++ Δ ++ Κ) ≡ (Γm ++ βΜ) ++ Δ ++ Κ
    flᵦʳ = flattenʳ Γm βΜ Δ Κ

    flʳΞᵦ : Ξ₁ ++ (βΜ ++ Δ ++ Κ) ≡ (Ξ₁ ++ βΜ) ++ Δ ++ Κ
    flʳΞᵦ = flattenʳ Ξ₁ βΜ Δ Κ

    flᵦR' : (Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ) ≡ Θ ++ Γ ++ (Ξ₁ ++ βΜ ++ Δ ++ Κ)
    flᵦR' = flattenˡ Θ Γ Ξ₁ (βΜ ++ Δ ++ Κ)

    qLᵇ : (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)
        ≡ ((Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    qLᵇ = bury (Θ ++ Γ ++ Ξ₁) Ψ Μᵧ (Δ ++ Κ)

    qR : (Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)
       ≡ Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ ++ Δ ++ Κ)
    qR = flattenˡ Θ Γ Ξ₁ (Ψ ++ Μᵧ ++ Δ ++ Κ)

    pRᵇ : Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    pRᵇ = bury Γm Ψ Μᵧ (Δ ++ Κ)

    bdᵦ : (Θ ++ Γ ++ (Ξ₁ ++ βΜ)) ++ Δ ++ Κ ≡ Θ ++ Γ ++ ((Ξ₁ ++ βΜ) ++ Δ ++ Κ)
    bdᵦ = interchangeₘ-boundary Θ Γ (Ξ₁ ++ βΜ) Δ Κ

    S : Split y (Θ ++ Γ ++ (Ξ₁ ++ Ψ ++ Μᵧ)) (Θ ++ Γ ++ (Ξ₁ ++ ΨΔ)) Κ
    S = split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ s₂c))

    Sᶜ : Split y ((Θ ++ Γ ++ Ξ₁) ++ (Ψ ++ Μᵧ)) ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) Κ
    Sᶜ = split-++ʳ (Θ ++ Γ ++ Ξ₁) s₂c

    QgRaw : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΔ)) C
    QgRaw = sub (split-++ˡ s₁' βΔ) Q g

    Qg : Tm ((Θ ++ Γ ++ Ξ₁) ++ βΔ) C
    Qg = cast (sym flᵦ) QgRaw

    W : Tm ((Θ ++ Γ ++ Ξ₁) ++ ΨΔ) C
    W = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Qg

    QhRaw : Tm ((Γm ++ βΜ) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ s₂ᵧ)) Q h

    Qh' : Tm (Γm ++ (βΜ ++ Δ ++ Κ)) C
    Qh' = cast (sym flᵦʳ) QhRaw

    innerL : Tm (((Θ ++ Γ ++ Ξ₁) ++ βΜ) ++ Δ ++ Κ) C
    innerL = sub (split-++ʳ (Θ ++ Γ ++ Ξ₁) (wrapβ s₂ᵧ)) Qg h

    uL' : Tm ((Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ)) C
    uL' = cast (sym flᵦL') innerL

    WL : Tm ((Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WL = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P uL'

    innerR : Tm (Θ ++ Γ ++ (Ξ₁ ++ βΜ ++ Δ ++ Κ)) C
    innerR = sub (split-++ˡ s₁' (βΜ ++ Δ ++ Κ)) Qh' g

    uR' : Tm ((Θ ++ Γ ++ Ξ₁) ++ (βΜ ++ Δ ++ Κ)) C
    uR' = cast (sym flᵦR') innerR

    WR' : Tm ((Θ ++ Γ ++ Ξ₁) ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WR' = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P uR'

    WRi : Tm (Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WRi = match𝟙 {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} P Qh'

    s₂ⁱ : Split y (Ξ₁ ++ βΜ) (Ξ₁ ++ βΔ) Κ
    s₂ⁱ = split-++ʳ Ξ₁ (wrapβ s₂ᵧ)

    ihL : Tm ((Θ ++ Γ ++ (Ξ₁ ++ βΜ)) ++ Δ ++ Κ) C
    ihL = sub (split-++ʳ Θ (split-++ʳ Γ s₂ⁱ)) QgRaw h

    ihR : Tm (Θ ++ Γ ++ ((Ξ₁ ++ βΜ) ++ Δ ++ Κ)) C
    ihR = sub (split-++ˡ (split-here Θ x (Ξ₁ ++ βΜ)) (Δ ++ Κ))
              (sub (split-behind (split-++ˡ s₁' βΔ) s₂ⁱ) Q h) g

    ih : PathP (λ i → Tm (bdᵦ i) C) ihL ihR
    ih = sub-interchange (split-++ˡ s₁' βΔ) s₂ⁱ Q g h

    π-in : PathP (λ i → Tm (flβΜ i ++ Δ ++ Κ) C) innerL ihL
    π-in i = sub (co-crossˡ Θ Γ Ξ₁ (wrapβ s₂ᵧ) i)
                 (symP (cast-filler (sym flᵦ) QgRaw) i) h

    e₆ : sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g ≡ ihR
    e₆ j = sub (co-crossʰ s₁' βΜ (Δ ++ Κ) j)
               (sub (split-behind-cross s₁' (wrapβ s₂ᵧ) j) Q h) g

    π-innR : PathP (λ i → Tm (Θ ++ Γ ++ sym flʳΞᵦ i) C)
               (sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g) innerR
    π-innR i = sub (symP (co-crossʳ s₁' βΜ Δ Κ) i)
                   (cast-filler (sym flᵦʳ) QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) i)) uL' ihL
    M₁ = _∙P_ {B = TmC} {p = flᵦL'} {q = ap (_++ Δ ++ Κ) flβΜ}
           (symP (cast-filler (sym flᵦL') innerL)) π-in

    M₂ : PathP (λ i → TmC (((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ) i))
           uL' (sub (split-++ˡ (split-++ˡ s₁' βΜ) (Δ ++ Κ)) QhRaw g)
    M₂ = _∙P_ {B = TmC} {p = flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ} {q = bdᵦ}
           M₁ (ih ▷ sym e₆)

    M₃ : PathP (λ i → TmC ((((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                            ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)) i))
           uL' innerR
    M₃ = _∙P_ {B = TmC} {p = (flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ}
           {q = ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)}
           M₂ π-innR

    M₄ : PathP (λ i → TmC (((((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                             ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)) ∙ sym flᵦR') i))
           uL' uR'
    M₄ = _∙P_ {B = TmC} {p = ((flᵦL' ∙ ap (_++ Δ ++ Κ) flβΜ) ∙ bdᵦ)
                             ∙ ap (λ l → Θ ++ Γ ++ l) (sym flʳΞᵦ)} {q = sym flᵦR'}
           M₃ (cast-filler (sym flᵦR') innerR)

    M : uL' ≡ uR'
    M = tm-over (sq-ΓΔ-inner Θ Γ Ξ₁ βΜ Δ Κ) M₄

    Wc : WL ≡ WR'
    Wc j = match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Μᵧ ++ Δ ++ Κ} P (M j)

    SRᶜ : Split x Θ (Γm ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)) (Ξ₁ ++ Ψ ++ Μᵧ ++ Δ ++ Κ)
    SRᶜ = split-++ˡ s₁' (Ψ ++ Μᵧ ++ Δ ++ Κ)

    SR₀ : Split x Θ ((Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ) ((Ξ₁ ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ)
    SR₀ = split-++ˡ (split-++ˡ s₁' (Ψ ++ Μᵧ)) (Δ ++ Κ)

    SR : Split x Θ ((Θ ++ x ∷ (Ξ₁ ++ Ψ ++ Μᵧ)) ++ Δ ++ Κ)
                 ((Ξ₁ ++ Ψ ++ Μᵧ) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here Θ x (Ξ₁ ++ Ψ ++ Μᵧ)) (Δ ++ Κ)

    e₁ : sub S (sub (split-++ˡ s₁' ΨΔ) T g) h ≡ sub S (cast flΨΔ W) h
    e₁ = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ˡ s₁' ΨΔ)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flΨΔ)

    ℓ₂ : PathP (λ i → Tm (flΨΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ W h) (sub S (cast flΨΔ W) h)
    ℓ₂ i = sub (co-crossˡ Θ Γ Ξ₁ s₂c i) (cast-filler flΨΔ W i) h

    e₂ : sub Sᶜ W h ≡ cast qLᵇ WL
    e₂ = ap (λ v → sub-match𝟙ˡ v P Qg h) (split-++-ʳ (Θ ++ Γ ++ Ξ₁) s₂c)
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Qg h) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) WL)
            (∙-idr (refl {x = (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ Μᵧ}))
       ∙ cast-∙idr qLᵇ WL

    e₄ : sub SRᶜ WRi g ≡ cast qR WR'
    e₄ = ap (λ v → sub-match𝟙ˡ v P Qh' g) (split-++-ˡ s₁' (Ψ ++ Μᵧ ++ Δ ++ Κ))
       ∙ cast-∙idr qR WR'

    π' : PathP (λ i → Tm (Θ ++ Γ ++ bury Ξ₁ Ψ Μᵧ (Δ ++ Κ) i) C)
           (sub SRᶜ WRi g) (sub SR₀ (cast pRᵇ WRi) g)
    π' i = sub (co-crossᵇ s₁' Ψ Μᵧ (Δ ++ Κ) i) (cast-filler pRᵇ WRi i) g

    e₃ : sub SR₀ (sub (split-++ʳ Γm s₂c) T h) g ≡ sub SR₀ (cast pRᵇ WRi) g
    e₃ = ap (λ v → sub SR₀ (sub-match𝟙ˡ v P Q h) g) (split-++-ʳ Γm s₂c)
       ∙ ap (λ v → sub SR₀ (sub-match𝟙ʳ v refl P Q h) g) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → sub SR₀ (cast (pRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRi) g)
            (∙-idr (refl {x = Γm ++ Ψ ++ Μᵧ}))
       ∙ ap (λ ρ → sub SR₀ (cast ρ WRi) g) (∙-idr pRᵇ)

    e₅ : sub SR₀ (sub (split-++ʳ Γm s₂c) T h) g
       ≡ sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂c)) T h) g
    e₅ j = sub (co-crossʰ s₁' (Ψ ++ Μᵧ) (Δ ++ Κ) j)
               (sub (split-behind-cross s₁' s₂c j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) i))
             (sub S (cast flΨΔ W) h) WL
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flΨΜ)} {q = sym qLᵇ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ WL))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR) i))
             (sub S (cast flΨΔ W) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ} {q = qR}
             (seg₁ ▷ Wc) (cast-filler qR WR')
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR)
                              ∙ ap (λ l → Θ ++ Γ ++ l) (bury Ξ₁ Ψ Μᵧ (Δ ++ Κ))) i))
             (sub S (cast flΨΔ W) h)
             (sub SR (sub (split-behind (split-++ˡ s₁' ΨΔ) (split-++ʳ Ξ₁ s₂c)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ) flΨΜ) ∙ sym qLᵇ) ∙ qR)}
             {q = ap (λ l → Θ ++ Γ ++ l) (bury Ξ₁ Ψ Μᵧ (Δ ++ Κ))}
             seg₂ π'
           ▷ (sym e₃ ∙ e₅)
core-m𝟙-ΨΨ {x = x} {y = y} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} {Κ₁ = Κ₁} s₁'' s₂'' P Q g h =
  tm-over (sq-ΨΨ Γm Θ₂ Γ Μ Δ Κ₁ Δm) (e₁ ◁ seg₄)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = 𝟙

    bdΘ₂ : (Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁ ≡ Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)
    bdΘ₂ = interchangeₘ-boundary Θ₂ Γ Μ Δ Κ₁

    flᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)
    flᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm

    flʳΜ : Γm ++ (Θ₂ ++ Γ ++ Μ) ≡ (Γm ++ Θ₂) ++ Γ ++ Μ
    flʳΜ = flattenʳ Γm Θ₂ Γ Μ

    qLᵐ : Γm ++ (((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁) ++ Δm)
        ≡ (Γm ++ (Θ₂ ++ Γ ++ Μ)) ++ Δ ++ (Κ₁ ++ Δm)
    qLᵐ = flattenᵐ Γm (Θ₂ ++ Γ ++ Μ) Δ Κ₁ Δm

    qRᵐ : Γm ++ ((Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) ++ Δm)
        ≡ (Γm ++ Θ₂) ++ Γ ++ ((Μ ++ Δ ++ Κ₁) ++ Δm)
    qRᵐ = flattenᵐ Γm Θ₂ Γ (Μ ++ Δ ++ Κ₁) Δm

    pRᵐ : Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm)
        ≡ (Γm ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ (Κ₁ ++ Δm)
    pRᵐ = flattenᵐ Γm (Θ₂ ++ x ∷ Μ) Δ Κ₁ Δm

    flΜΔm : (Μ ++ Δ ++ Κ₁) ++ Δm ≡ Μ ++ Δ ++ (Κ₁ ++ Δm)
    flΜΔm = flattenˡ Μ Δ Κ₁ Δm

    s₂ᶜ : Split y Μ (Ξ₁ ++ Δm) (Κ₁ ++ Δm)
    s₂ᶜ = split-++ˡ s₂'' Δm

    S : Split y ((Γm ++ Θ₂) ++ Γ ++ Μ) ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)) (Κ₁ ++ Δm)
    S = split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ s₂ᶜ)

    S₀' : Split y (Θ₂ ++ Γ ++ Μ) (Θ₂ ++ Γ ++ Ξ₁) Κ₁
    S₀' = split-++ʳ Θ₂ (split-++ʳ Γ s₂'')

    Sᵐ : Split y (Θ₂ ++ Γ ++ Μ) ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) (Κ₁ ++ Δm)
    Sᵐ = split-++ˡ S₀' Δm

    Sᶜ : Split y (Γm ++ (Θ₂ ++ Γ ++ Μ)) (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) (Κ₁ ++ Δm)
    Sᶜ = split-++ʳ Γm Sᵐ

    Wg : Tm (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) C
    Wg = match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁'' P g) Q

    ihL : Tm ((Θ₂ ++ Γ ++ Μ) ++ Δ ++ Κ₁) AB
    ihL = sub S₀' (sub s₁'' P g) h

    SB : Split y (Θ₂ ++ x ∷ Μ) Ψ Κ₁
    SB = split-behind s₁'' s₂''

    SR₁ : Split x Θ₂ ((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) (Μ ++ Δ ++ Κ₁)
    SR₁ = split-++ˡ (split-here Θ₂ x Μ) (Δ ++ Κ₁)

    ihR : Tm (Θ₂ ++ Γ ++ (Μ ++ Δ ++ Κ₁)) AB
    ihR = sub SR₁ (sub SB P h) g

    ih : PathP (λ i → Tm (bdΘ₂ i) AB) ihL ihR
    ih = sub-interchange s₁'' s₂'' P g h

    WRᵇ : Tm (Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm)) C
    WRᵇ = match𝟙 {Γ = Γm} {Δ = Δm} (sub SB P h) Q

    SRᵐ : Split x Θ₂ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm) ((Μ ++ Δ ++ Κ₁) ++ Δm)
    SRᵐ = split-++ˡ SR₁ Δm

    SRᶜ : Split x (Γm ++ Θ₂) (Γm ++ (((Θ₂ ++ x ∷ Μ) ++ Δ ++ Κ₁) ++ Δm))
                  ((Μ ++ Δ ++ Κ₁) ++ Δm)
    SRᶜ = split-++ʳ Γm SRᵐ

    SRb : Split x (Γm ++ Θ₂) ((Γm ++ (Θ₂ ++ x ∷ Μ)) ++ Δ ++ (Κ₁ ++ Δm))
                  (Μ ++ Δ ++ (Κ₁ ++ Δm))
    SRb = split-++ˡ (split-++ʳ Γm (split-here Θ₂ x Μ)) (Δ ++ Κ₁ ++ Δm)

    SR : Split x (Γm ++ Θ₂) (((Γm ++ Θ₂) ++ x ∷ Μ) ++ Δ ++ (Κ₁ ++ Δm))
                 (Μ ++ Δ ++ (Κ₁ ++ Δm))
    SR = split-++ˡ (split-here (Γm ++ Θ₂) x Μ) (Δ ++ Κ₁ ++ Δm)

    e₁ : sub S (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᵐ Wg) h
    e₁ = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁'' Δm))
       ∙ ap (λ v → sub S (sub-match𝟙ʳ v refl P Q g) h) (split-++-ˡ s₁'' Δm)
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr flᵐ)

    ℓ₂ : PathP (λ i → Tm (flʳΜ i ++ Δ ++ (Κ₁ ++ Δm)) C)
           (sub Sᶜ Wg h) (sub S (cast flᵐ Wg) h)
    ℓ₂ i = sub (co-mid Γm Θ₂ Γ s₂'' Δm i) (cast-filler flᵐ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)
    e₂ = ap (λ v → sub-match𝟙ˡ v (sub s₁'' P g) Q h) (split-++-ʳ Γm Sᵐ)
       ∙ ap (λ v → sub-match𝟙ʳ v refl (sub s₁'' P g) Q h) (split-++-ˡ S₀' Δm)
       ∙ cast-∙idr qLᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)

    eV : sub SRᶜ WRᵇ g ≡ cast qRᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihR Q)
    eV = ap (λ v → sub-match𝟙ˡ v (sub SB P h) Q g) (split-++-ʳ Γm SRᵐ)
       ∙ ap (λ v → sub-match𝟙ʳ v refl (sub SB P h) Q g) (split-++-ˡ SR₁ Δm)
       ∙ cast-∙idr qRᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihR Q)

    π'R : PathP (λ i → Tm ((Γm ++ Θ₂) ++ Γ ++ flΜΔm i) C)
            (sub SRᶜ WRᵇ g) (sub SRb (cast pRᵐ WRᵇ) g)
    π'R i = sub (co-midʰ Γm Θ₂ x Μ Δ Κ₁ Δm i) (cast-filler pRᵐ WRᵇ i) g

    eR : sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) s₂ᶜ)
                     (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g
       ≡ sub SRb (cast pRᵐ WRᵇ) g
    eR = (λ j → sub (split-++ˡ (symP (split-here-++ʳ Γm Θ₂ x Μ) j) (Δ ++ Κ₁ ++ Δm))
                    (sub (split-behind-++ʳ Γm (split-++ˡ s₁'' Δm) s₂ᶜ j)
                         (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)
       ∙ ap (λ s → sub SRb (sub (split-++ʳ Γm s) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)
            (split-behind-++ˡ s₁'' s₂'' Δm)
       ∙ ap (λ v → sub SRb (sub-match𝟙ˡ v P Q h) g)
            (split-++-ʳ Γm (split-++ˡ SB Δm))
       ∙ ap (λ v → sub SRb (sub-match𝟙ʳ v refl P Q h) g) (split-++-ˡ SB Δm)
       ∙ ap (λ ρ → sub SRb (cast ρ WRᵇ) g) (∙-idr pRᵐ)

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ) i))
             (sub S (cast flᵐ Wg) h) (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ)} {q = sym qLᵐ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                              ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) i))
             (sub S (cast flᵐ Wg) h) (match𝟙 {Γ = Γm} {Δ = Δm} ihR Q)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ}
             {q = ap (λ l → Γm ++ l ++ Δm) bdΘ₂}
             seg₁ (λ j → match𝟙 {Γ = Γm} {Δ = Δm} (ih j) Q)

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                               ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ) i))
             (sub S (cast flᵐ Wg) h) (sub SRᶜ WRᵇ g)
    seg₃ = _∙P_ {B = TmC} {p = (sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                               ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂} {q = qRᵐ}
             seg₂ (cast-filler qRᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihR Q))
           ▷ sym eV

    seg₄ : PathP (λ i → TmC (((((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                                ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ)
                              ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flΜΔm) i))
             (sub S (cast flᵐ Wg) h)
             (sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) s₂ᶜ)
                          (match𝟙 {Γ = Γm} {Δ = Δm} P Q) h) g)
    seg₄ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ₁ ++ Δm) flʳΜ) ∙ sym qLᵐ)
                                ∙ ap (λ l → Γm ++ l ++ Δm) bdΘ₂) ∙ qRᵐ}
             {q = ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flΜΔm}
             seg₃ π'R
           ▷ sym eR
core-m𝟙-ΨΔ {x = x} {y = y} {C = C} {Θ₂ = Θ₂} {Γ = Γ} {Μᵧ = Μᵧ} {Δ = Δ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} {Ξ₁ = Ξ₁} s₁'' s₂ᵧ P Q g h =
  tm-over (sq-ΨΔ Γm Θ₂ Γ Ξ₁ Μᵧ Δ Κ) (e₁ ◁ seg₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    AB : Ty
    AB = 𝟙

    βΜ : Ctx
    βΜ = Μᵧ

    wrapβ : ∀ {y' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split y' Θ' Λ Ξ' → Split y' (Θ') (Λ) Ξ'
    wrapβ = split-++ʳ ([])

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match𝟙 {Γ = Γm} {Δ = Δm} P Q

    flᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)
    flᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm

    flᵐΜ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ)
    flᵐΜ = flattenᵐ Γm Θ₂ Γ Ξ₁ Μᵧ

    qLᵇ : Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ)
        ≡ (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ)) ++ Δ ++ Κ
    qLᵇ = bury Γm (Θ₂ ++ Γ ++ Ξ₁) Μᵧ (Δ ++ Κ)

    qRᵐ : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ))
        ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ ++ Δ ++ Κ)
    qRᵐ = flattenᵐ Γm Θ₂ Γ Ξ₁ (Μᵧ ++ Δ ++ Κ)

    pRᵇ : Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ
    pRᵇ = bury Γm Ψ Μᵧ (Δ ++ Κ)

    flᵦʳ : Γm ++ (βΜ ++ Δ ++ Κ) ≡ (Γm ++ βΜ) ++ Δ ++ Κ
    flᵦʳ = flattenʳ Γm βΜ Δ Κ

    flʳΞΜ : Ξ₁ ++ (Μᵧ ++ Δ ++ Κ) ≡ (Ξ₁ ++ Μᵧ) ++ Δ ++ Κ
    flʳΞΜ = flattenʳ Ξ₁ Μᵧ Δ Κ

    Pg : Tm (Θ₂ ++ Γ ++ Ξ₁) AB
    Pg = sub s₁'' P g

    Wg : Tm (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) C
    Wg = match𝟙 {Γ = Γm} {Δ = Δm} Pg Q

    QhRaw : Tm ((Γm ++ βΜ) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ s₂ᵧ)) Q h

    Qh' : Tm (Γm ++ (βΜ ++ Δ ++ Κ)) C
    Qh' = cast (sym flᵦʳ) QhRaw

    X : Tm (Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ (Μᵧ ++ Δ ++ Κ)) C
    X = match𝟙 {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} Pg Qh'

    WRi : Tm (Γm ++ Ψ ++ (Μᵧ ++ Δ ++ Κ)) C
    WRi = match𝟙 {Γ = Γm} {Δ = Μᵧ ++ Δ ++ Κ} P Qh'

    S : Split y ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Μᵧ)) ((Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δm)) Κ
    S = split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-++ʳ Ξ₁ s₂ᵧ))

    Sᶜ : Split y (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ)) (Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm)) Κ
    Sᶜ = split-++ʳ Γm (split-++ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ)

    SRᶜ : Split x (Γm ++ Θ₂) (Γm ++ (Ψ ++ Μᵧ ++ Δ ++ Κ)) (Ξ₁ ++ Μᵧ ++ Δ ++ Κ)
    SRᶜ = split-++ʳ Γm (split-++ˡ s₁'' (Μᵧ ++ Δ ++ Κ))

    SRb₀ : Split x (Γm ++ Θ₂) ((Γm ++ (Ψ ++ Μᵧ)) ++ Δ ++ Κ) ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SRb₀ = split-++ˡ (split-++ʳ Γm (split-++ˡ s₁'' Μᵧ)) (Δ ++ Κ)

    SRb₁ : Split x (Γm ++ Θ₂) ((Γm ++ (Θ₂ ++ x ∷ (Ξ₁ ++ Μᵧ))) ++ Δ ++ Κ)
                   ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SRb₁ = split-++ˡ (split-++ʳ Γm (split-here Θ₂ x (Ξ₁ ++ Μᵧ))) (Δ ++ Κ)

    SR : Split x (Γm ++ Θ₂) (((Γm ++ Θ₂) ++ x ∷ (Ξ₁ ++ Μᵧ)) ++ Δ ++ Κ)
                 ((Ξ₁ ++ Μᵧ) ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γm ++ Θ₂) x (Ξ₁ ++ Μᵧ)) (Δ ++ Κ)

    e₁ : sub S (sub (split-++ʳ Γm (split-++ˡ s₁'' Δm)) T g) h ≡ sub S (cast flᵐ Wg) h
    e₁ = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁'' Δm))
       ∙ ap (λ v → sub S (sub-match𝟙ʳ v refl P Q g) h) (split-++-ˡ s₁'' Δm)
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr flᵐ)

    ℓ₂ : PathP (λ i → Tm (flᵐΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ Wg h) (sub S (cast flᵐ Wg) h)
    ℓ₂ i = sub (co-midᵧ Γm Θ₂ Γ Ξ₁ s₂ᵧ i) (cast-filler flᵐ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵇ X
    e₂ = ap (λ v → sub-match𝟙ˡ v Pg Q h) (split-++-ʳ Γm (split-++ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ))
       ∙ ap (λ v → sub-match𝟙ʳ v refl Pg Q h) (split-++-ʳ (Θ₂ ++ Γ ++ Ξ₁) s₂ᵧ)
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) X)
            (∙-idr (refl {x = Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ Μᵧ}))
       ∙ cast-∙idr qLᵇ X

    e₄ : sub SRᶜ WRi g ≡ cast qRᵐ X
    e₄ = ap (λ v → sub-match𝟙ˡ v P Qh' g) (split-++-ʳ Γm (split-++ˡ s₁'' (Μᵧ ++ Δ ++ Κ)))
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Qh' g) (split-++-ˡ s₁'' (Μᵧ ++ Δ ++ Κ))
       ∙ cast-∙idr qRᵐ X

    π' : PathP (λ i → Tm ((Γm ++ Θ₂) ++ Γ ++ flʳΞΜ i) C)
           (sub SRᶜ WRi g) (sub SRb₀ (cast pRᵇ WRi) g)
    π' i = sub (co-midᵇ Γm s₁'' Μᵧ Δ Κ i) (cast-filler pRᵇ WRi i) g

    e₃ : sub SRb₀ (sub (split-++ʳ Γm (split-++ʳ Ψ s₂ᵧ)) T h) g
       ≡ sub SRb₀ (cast pRᵇ WRi) g
    e₃ = ap (λ v → sub SRb₀ (sub-match𝟙ˡ v P Q h) g) (split-++-ʳ Γm (split-++ʳ Ψ s₂ᵧ))
       ∙ ap (λ v → sub SRb₀ (sub-match𝟙ʳ v refl P Q h) g) (split-++-ʳ Ψ s₂ᵧ)
       ∙ ap (λ ρ → sub SRb₀ (cast (pRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRi) g)
            (∙-idr (refl {x = Γm ++ Ψ ++ Μᵧ}))
       ∙ ap (λ ρ → sub SRb₀ (cast ρ WRi) g) (∙-idr pRᵇ)

    c₂ : sub SRb₀ (sub (split-++ʳ Γm (split-++ʳ Ψ s₂ᵧ)) T h) g
       ≡ sub SRb₁ (sub (split-++ʳ Γm (split-behind (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ))) T h) g
    c₂ j = sub (split-++ˡ (split-++ʳ Γm (co-crossᵖ s₁'' Μᵧ j)) (Δ ++ Κ))
               (sub (split-++ʳ Γm (split-behind-cross s₁'' s₂ᵧ j)) T h) g

    c₁ : sub SRb₁ (sub (split-++ʳ Γm (split-behind (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ))) T h) g
       ≡ sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ)) T h) g
    c₁ j = sub (split-++ˡ (split-here-++ʳ Γm Θ₂ x (Ξ₁ ++ Μᵧ) j) (Δ ++ Κ))
               (sub (symP (split-behind-++ʳ Γm (split-++ˡ s₁'' Δm) (split-++ʳ Ξ₁ s₂ᵧ)) j) T h) g

    seg₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) i))
             (sub S (cast flᵐ Wg) h) X
    seg₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flᵐΜ)} {q = sym qLᵇ}
             (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ X))

    seg₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ) i))
             (sub S (cast flᵐ Wg) h) (sub SRᶜ WRi g)
    seg₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ} {q = qRᵐ}
             seg₁ (cast-filler qRᵐ X)
           ▷ sym e₄

    seg₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ)
                              ∙ ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flʳΞΜ) i))
             (sub S (cast flᵐ Wg) h)
             (sub SR (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' Δm)) (split-++ʳ Ξ₁ s₂ᵧ)) T h) g)
    seg₃ = _∙P_ {B = TmC} {p = ((sym (ap (_++ Δ ++ Κ) flᵐΜ) ∙ sym qLᵇ) ∙ qRᵐ)}
             {q = ap (λ l → (Γm ++ Θ₂) ++ Γ ++ l) flʳΞΜ}
             seg₂ π'
           ▷ (sym e₃ ∙ c₂ ∙ c₁)
core-m𝟙-ΔΔ {x = x} {y = y} {C = C} {Θ₃ = Θ₃} {Γ = Γ} {Μ = Μ} {Δ = Δ} {Ξ = Ξ} {Κ = Κ} {Ψ = Ψ} {Γm = Γm} {Δm = Δm} s₁'' s₂ P Q g h =
  tm-over (sq-ΔΔ-outer Γm Ψ Θ₃ Γ Μ Δ Κ) (e₁ ◁ segO₃)
  where
    TmC : Ctx → Type _
    TmC Ω = Tm Ω C

    βctx : Ctx → Ctx
    βctx l = l

    wrapβ : ∀ {x' : Ty} {Θ' Λ Ξ' : Ctx}
          → Split x' Θ' Λ Ξ' → Split x' (βctx Θ') (βctx Λ) Ξ'
    wrapβ = split-++ʳ []

    T : Tm (Γm ++ Ψ ++ Δm) C
    T = match𝟙 {Γ = Γm} {Δ = Δm} P Q

    bdΘ₃ : (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdΘ₃ = interchangeₘ-boundary Θ₃ Γ Μ Δ Κ

    bdᵦ : ((Γm ++ βctx Θ₃) ++ Γ ++ Μ) ++ Δ ++ Κ
        ≡ (Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    bdᵦ = interchangeₘ-boundary (Γm ++ βctx Θ₃) Γ Μ Δ Κ

    buryΞ : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ Ξ
    buryΞ = bury Γm Ψ Θ₃ (Γ ++ Ξ)

    buryΜ : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ Μ
    buryΜ = bury Γm Ψ Θ₃ (Γ ++ Μ)

    qLᵇ : Γm ++ Ψ ++ ((Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)
        ≡ (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ
    qLᵇ = bury Γm Ψ (Θ₃ ++ Γ ++ Μ) (Δ ++ Κ)

    qRᵇ : Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)
        ≡ (Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ
    qRᵇ = bury Γm Ψ (Θ₃ ++ x ∷ Μ) (Δ ++ Κ)

    qRc : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))
        ≡ (Γm ++ Ψ ++ Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    qRc = bury Γm Ψ Θ₃ (Γ ++ Μ ++ Δ ++ Κ)

    flᵦˡ : Γm ++ βctx (Θ₃ ++ Γ ++ Ξ) ≡ (Γm ++ βctx Θ₃) ++ Γ ++ Ξ
    flᵦˡ = flattenʳ Γm (βctx Θ₃) Γ Ξ

    flᵦΜ : Γm ++ βctx (Θ₃ ++ Γ ++ Μ) ≡ (Γm ++ βctx Θ₃) ++ Γ ++ Μ
    flᵦΜ = flattenʳ Γm (βctx Θ₃) Γ Μ

    flᵦL' : Γm ++ (βctx (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)
          ≡ (Γm ++ βctx (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ
    flᵦL' = flattenʳ Γm (βctx (Θ₃ ++ Γ ++ Μ)) Δ Κ

    flᵦʳ' : Γm ++ (βctx (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)
          ≡ (Γm ++ βctx (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ
    flᵦʳ' = flattenʳ Γm (βctx (Θ₃ ++ x ∷ Μ)) Δ Κ

    flᵦR' : Γm ++ βctx (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))
          ≡ (Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)
    flᵦR' = flattenʳ Γm (βctx Θ₃) Γ (Μ ++ Δ ++ Κ)

    s₁ᶜ : Split x (Γm ++ Ψ ++ Θ₃) (Γm ++ Ψ ++ Δm) Ξ
    s₁ᶜ = split-++ʳ Γm (split-++ʳ Ψ s₁'')

    S : Split y ((Γm ++ Ψ ++ Θ₃) ++ Γ ++ Μ) ((Γm ++ Ψ ++ Θ₃) ++ Γ ++ Ξ) Κ
    S = split-++ʳ (Γm ++ Ψ ++ Θ₃) (split-++ʳ Γ s₂)

    S₂' : Split y (Θ₃ ++ Γ ++ Μ) (Θ₃ ++ Γ ++ Ξ) Κ
    S₂' = split-++ʳ Θ₃ (split-++ʳ Γ s₂)

    Sᶜ : Split y (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)) (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ)) Κ
    Sᶜ = split-++ʳ Γm (split-++ʳ Ψ S₂')

    QgRaw : Tm ((Γm ++ βctx Θ₃) ++ Γ ++ Ξ) C
    QgRaw = sub (split-++ʳ Γm (wrapβ s₁'')) Q g

    Qg : Tm (Γm ++ βctx (Θ₃ ++ Γ ++ Ξ)) C
    Qg = cast (sym flᵦˡ) QgRaw

    Wg : Tm (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ)) C
    Wg = match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P Qg

    innerL : Tm ((Γm ++ βctx (Θ₃ ++ Γ ++ Μ)) ++ Δ ++ Κ) C
    innerL = sub (split-++ʳ Γm (wrapβ S₂')) Qg h

    uL : Tm (Γm ++ (βctx (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)) C
    uL = cast (sym flᵦL') innerL

    WLᵇ : Tm (Γm ++ Ψ ++ ((Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ)) C
    WLᵇ = match𝟙 {Γ = Γm} {Δ = (Θ₃ ++ Γ ++ Μ) ++ Δ ++ Κ} P uL

    SBh : Split y (Θ₃ ++ x ∷ Μ) Δm Κ
    SBh = split-behind s₁'' s₂

    QhRaw : Tm ((Γm ++ βctx (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ) C
    QhRaw = sub (split-++ʳ Γm (wrapβ SBh)) Q h

    sᵦ : Split x (βctx Θ₃) (βctx (Θ₃ ++ x ∷ Μ)) Μ
    sᵦ = split-++ʳ [] (split-here Θ₃ x Μ)

    SR₃ : Split x Θ₃ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ) (Μ ++ Δ ++ Κ)
    SR₃ = split-++ˡ (split-here Θ₃ x Μ) (Δ ++ Κ)

    SRᵦ' : Split x (Γm ++ βctx Θ₃) (Γm ++ (βctx (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ))
                   (Μ ++ Δ ++ Κ)
    SRᵦ' = split-++ʳ Γm (wrapβ SR₃)

    innerR : Tm ((Γm ++ βctx Θ₃) ++ Γ ++ (Μ ++ Δ ++ Κ)) C
    innerR = sub SRᵦ' (cast (sym flᵦʳ') QhRaw) g

    uR : Tm (Γm ++ βctx (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))) C
    uR = cast (sym flᵦR') innerR

    WRᵇ' : Tm (Γm ++ Ψ ++ (Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ))) C
    WRᵇ' = match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Γ ++ (Μ ++ Δ ++ Κ)} P uR

    ihLt : Tm (((Γm ++ βctx Θ₃) ++ Γ ++ Μ) ++ Δ ++ Κ) C
    ihLt = sub (split-++ʳ (Γm ++ βctx Θ₃) (split-++ʳ Γ s₂)) QgRaw h

    ih : PathP (λ i → Tm (bdᵦ i) C)
           ihLt
           (sub (split-++ˡ (split-here (Γm ++ βctx Θ₃) x Μ) (Δ ++ Κ))
                (sub (split-behind (split-++ʳ Γm (wrapβ s₁'')) s₂) Q h) g)
    ih = sub-interchange (split-++ʳ Γm (wrapβ s₁'')) s₂ Q g h

    π-in : PathP (λ i → Tm (flᵦΜ i ++ Δ ++ Κ) C) innerL ihLt
    π-in i = sub (co-ʳʳʳ Γm (βctx Θ₃) Γ s₂ i)
                 (symP (cast-filler (sym flᵦˡ) QgRaw) i) h

    b₁ : sub (split-++ˡ (split-here (Γm ++ βctx Θ₃) x Μ) (Δ ++ Κ))
             (sub (split-behind (split-++ʳ Γm (wrapβ s₁'')) s₂) Q h) g
       ≡ sub (split-++ˡ (split-++ʳ Γm (split-here (βctx Θ₃) x Μ)) (Δ ++ Κ))
             (sub (split-++ʳ Γm (split-behind (wrapβ s₁'') s₂)) Q h) g
    b₁ j = sub (split-++ˡ (symP (split-here-++ʳ Γm (βctx Θ₃) x Μ) j) (Δ ++ Κ))
               (sub (split-behind-++ʳ Γm (wrapβ s₁'') s₂ j) Q h) g

    b₂ : sub (split-++ˡ (split-++ʳ Γm (split-here (βctx Θ₃) x Μ)) (Δ ++ Κ))
             (sub (split-++ʳ Γm (split-behind (wrapβ s₁'') s₂)) Q h) g
       ≡ sub (split-++ˡ (split-++ʳ Γm sᵦ) (Δ ++ Κ)) QhRaw g
    b₂ j = sub (split-++ˡ (split-++ʳ Γm (symP (split-here-++ʳ [] Θ₃ x Μ) j))
                          (Δ ++ Κ))
               (sub (split-++ʳ Γm (split-behind-++ʳ [] s₁'' s₂ j)) Q h) g

    π-innR : sub (split-++ˡ (split-++ʳ Γm sᵦ) (Δ ++ Κ)) QhRaw g ≡ innerR
    π-innR i = sub (symP (co-flʳˡ Γm sᵦ Δ Κ) i)
                   (cast-filler (sym flᵦʳ') QhRaw i) g

    M₁ : PathP (λ i → TmC ((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) i)) uL ihLt
    M₁ = _∙P_ {B = TmC} {p = flᵦL'} {q = ap (_++ Δ ++ Κ) flᵦΜ}
           (symP (cast-filler (sym flᵦL') innerL)) π-in

    M₂ : PathP (λ i → TmC (((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ) i)) uL innerR
    M₂ = _∙P_ {B = TmC} {p = flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ} {q = bdᵦ}
           M₁ (ih ▷ (b₁ ∙ b₂ ∙ π-innR))

    M₃ : PathP (λ i → TmC ((((flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ) ∙ sym flᵦR') i))
           uL uR
    M₃ = _∙P_ {B = TmC} {p = (flᵦL' ∙ ap (_++ Δ ++ Κ) flᵦΜ) ∙ bdᵦ} {q = sym flᵦR'}
           M₂ (cast-filler (sym flᵦR') innerR)

    sq-inner : ∀ (Γ₁ : Ctx)
      → ((flattenʳ Γ₁ (βctx (Θ₃ ++ Γ ++ Μ)) Δ Κ
          ∙ ap (_++ Δ ++ Κ) (flattenʳ Γ₁ (βctx Θ₃) Γ Μ))
         ∙ interchangeₘ-boundary (Γ₁ ++ βctx Θ₃) Γ Μ Δ Κ)
        ∙ sym (flattenʳ Γ₁ (βctx Θ₃) Γ (Μ ++ Δ ++ Κ))
      ≡ ap (λ l → Γ₁ ++ βctx l) (interchangeₘ-boundary Θ₃ Γ Μ Δ Κ)
    sq-inner Γ₁ = list!

    M : PathP (λ j → TmC (ap (λ l → Γm ++ βctx l) bdΘ₃ j)) uL uR
    M = tm-over (sq-inner Γm) M₃

    Wc : PathP (λ j → TmC (Γm ++ Ψ ++ bdΘ₃ j)) WLᵇ WRᵇ'
    Wc j = match𝟙 {Γ = Γm} {Δ = bdΘ₃ j} P (M j)

    WRb : Tm (Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ)) C
    WRb = match𝟙 {Γ = Γm} {Δ = (Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ} P (cast (sym flᵦʳ') QhRaw)

    SRᶜb : Split x (Γm ++ Ψ ++ Θ₃) (Γm ++ Ψ ++ ((Θ₃ ++ x ∷ Μ) ++ Δ ++ Κ))
                   (Μ ++ Δ ++ Κ)
    SRᶜb = split-++ʳ Γm (split-++ʳ Ψ SR₃)

    SRb : Split x (Γm ++ Ψ ++ Θ₃) ((Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)) ++ Δ ++ Κ)
                  (Μ ++ Δ ++ Κ)
    SRb = split-++ˡ (split-++ʳ Γm (split-++ʳ Ψ (split-here Θ₃ x Μ))) (Δ ++ Κ)

    SR : Split x (Γm ++ Ψ ++ Θ₃) (((Γm ++ Ψ ++ Θ₃) ++ x ∷ Μ) ++ Δ ++ Κ)
                 (Μ ++ Δ ++ Κ)
    SR = split-++ˡ (split-here (Γm ++ Ψ ++ Θ₃) x Μ) (Δ ++ Κ)

    e₁ : sub S (sub s₁ᶜ T g) h ≡ sub S (cast buryΞ Wg) h
    e₁ = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ʳ Γm (split-++ʳ Ψ s₁''))
       ∙ ap (λ v → sub S (sub-match𝟙ʳ v refl P Q g) h) (split-++-ʳ Ψ s₁'')
       ∙ ap (λ ρ → sub S (cast (buryΞ ∙ ap (_++ Γ ++ Ξ) ρ) Wg) h) (∙-idr (refl {x = Γm ++ Ψ ++ Θ₃}))
       ∙ ap (λ ρ → sub S (cast ρ Wg) h) (∙-idr buryΞ)

    ℓ₂ : PathP (λ i → Tm (buryΜ i ++ Δ ++ Κ) C)
           (sub Sᶜ Wg h) (sub S (cast buryΞ Wg) h)
    ℓ₂ i = sub (co-bury Γm Ψ Θ₃ Γ s₂ i) (cast-filler buryΞ Wg i) h

    e₂ : sub Sᶜ Wg h ≡ cast qLᵇ WLᵇ
    e₂ = ap (λ v → sub-match𝟙ˡ v P Qg h) (split-++-ʳ Γm (split-++ʳ Ψ S₂'))
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Qg h) (split-++-ʳ Ψ S₂')
       ∙ ap (λ ρ → cast (qLᵇ ∙ ap (_++ Δ ++ Κ) ρ) WLᵇ) (∙-idr (refl {x = Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Μ)}))
       ∙ cast-∙idr qLᵇ WLᵇ

    eV : sub SRᶜb WRb g ≡ cast qRc WRᵇ'
    eV = ap (λ v → sub-match𝟙ˡ v P (cast (sym flᵦʳ') QhRaw) g)
            (split-++-ʳ Γm (split-++ʳ Ψ SR₃))
       ∙ ap (λ v → sub-match𝟙ʳ v refl P (cast (sym flᵦʳ') QhRaw) g)
            (split-++-ʳ Ψ SR₃)
       ∙ ap (λ ρ → cast (qRc ∙ ap (_++ Γ ++ Μ ++ Δ ++ Κ) ρ) WRᵇ') (∙-idr (refl {x = Γm ++ Ψ ++ Θ₃}))
       ∙ cast-∙idr qRc WRᵇ'

    π'R : sub SRᶜb WRb g ≡ sub SRb (cast qRᵇ WRb) g
    π'R i = sub (co-buryʰ Γm Ψ Θ₃ x Μ (Δ ++ Κ) i) (cast-filler qRᵇ WRb i) g

    eR : sub SR (sub (split-behind s₁ᶜ s₂) T h) g ≡ sub SRb (cast qRᵇ WRb) g
    eR = (λ j → sub (split-++ˡ (symP (split-here-++ʳ Γm (Ψ ++ Θ₃) x Μ) j) (Δ ++ Κ))
                    (sub (split-behind-++ʳ Γm (split-++ʳ Ψ s₁'') s₂ j) T h) g)
       ∙ (λ j → sub (split-++ˡ (split-++ʳ Γm (symP (split-here-++ʳ Ψ Θ₃ x Μ) j))
                               (Δ ++ Κ))
                    (sub (split-++ʳ Γm (split-behind-++ʳ Ψ s₁'' s₂ j)) T h) g)
       ∙ ap (λ v → sub SRb (sub-match𝟙ˡ v P Q h) g)
            (split-++-ʳ Γm (split-++ʳ Ψ SBh))
       ∙ ap (λ v → sub SRb (sub-match𝟙ʳ v refl P Q h) g) (split-++-ʳ Ψ SBh)
       ∙ ap (λ ρ → sub SRb (cast (qRᵇ ∙ ap (_++ Δ ++ Κ) ρ) WRb) g) (∙-idr (refl {x = Γm ++ Ψ ++ (Θ₃ ++ x ∷ Μ)}))
       ∙ ap (λ ρ → sub SRb (cast ρ WRb) g) (∙-idr qRᵇ)

    segO₁ : PathP (λ i → TmC ((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ) i))
              (sub S (cast buryΞ Wg) h) WLᵇ
    segO₁ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) buryΜ)} {q = sym qLᵇ}
              (symP ℓ₂ ▷ e₂) (symP (cast-filler qLᵇ WLᵇ))

    segO₂ : PathP (λ i → TmC (((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                               ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃) i))
              (sub S (cast buryΞ Wg) h) WRᵇ'
    segO₂ = _∙P_ {B = TmC} {p = sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ}
              {q = ap (λ l → Γm ++ Ψ ++ l) bdΘ₃}
              segO₁ Wc

    segO₃ : PathP (λ i → TmC ((((sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                                ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃) ∙ qRc) i))
              (sub S (cast buryΞ Wg) h)
              (sub SR (sub (split-behind s₁ᶜ s₂) T h) g)
    segO₃ = _∙P_ {B = TmC} {p = (sym (ap (_++ Δ ++ Κ) buryΜ) ∙ sym qLᵇ)
                                ∙ ap (λ l → Γm ++ Ψ ++ l) bdΘ₃} {q = qRc}
              segO₂ (cast-filler qRc WRᵇ')
            ▷ (sym eV ∙ π'R ∙ sym eR)
