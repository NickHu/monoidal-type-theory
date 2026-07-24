open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List

open import Multicategory.Free

module Multicategory.Free.Kit {o h} (G : Multigraph o h) where

open Syntax G public

-- Transport kit for the substitution calculus, in the style of ∘ₘ-subst /
-- ∘ₘ-pathp: every heterogeneous congruence is the operation applied under
-- the interval — no J anywhere.  Downstream files (SplitLemmas, Identity,
-- Assoc, Interchange, Descent) build on these.

private variable
  x y z A B C : Ty
  Γ Γ' Δ Θ Θ' Ξ Ξ' Ψ Ρ Ρ' Λ Μ Κ : Ctx
  As : List (Multigraph.Ob G)

-- cast is transport in the context index; its filler is the PathP form,
-- which is how proofs should consume it.
cast-filler : (p : Ρ ≡ Γ) (t : Tm Ρ z) → PathP (λ i → Tm (p i) z) t (cast p t)
cast-filler p t = transport-filler (λ i → Tm (p i) _) t

sp-cast-filler : (p : Ρ ≡ Γ) (ts : Sp Ρ As) → PathP (λ i → Sp (p i) As) ts (sp-cast p ts)
sp-cast-filler p ts = transport-filler (λ i → Sp (p i) _) ts

-- The congruence _≈_ transports along context paths (≈ applied under the
-- interval to the two cast fillers).
cast-≈ : {t t' : Tm Ρ z} (p : Ρ ≡ Γ) → t ≈ t' → cast p t ≈ cast p t'
cast-≈ {t = t} {t' = t'} p e =
  transport (λ i → cast-filler p t i ≈ cast-filler p t' i) e

-- The spine analogue: _≈ₛ_ transported along the two sp-cast fillers.
sp-cast-≈ₛ : {ts ts' : Sp Ρ As} (p : Ρ ≡ Γ)
           → ts ≈ₛ ts' → sp-cast p ts ≈ₛ sp-cast p ts'
sp-cast-≈ₛ {ts = ts} {ts' = ts'} p e =
  transport (λ i → sp-cast-filler p ts i ≈ₛ sp-cast-filler p ts' i) e

-- Collapse the ∙ refl left over by the p/q component of a view computation.
cast-∙idr : (p : Ρ ≡ Γ) (t : Tm Ρ z) → cast (p ∙ refl) t ≡ cast p t
cast-∙idr p t = ap (λ ρ → cast ρ t) (∙-idr p)

sp-cast-∙idr : (p : Ρ ≡ Γ) (ts : Sp Ρ As) → sp-cast (p ∙ refl) ts ≡ sp-cast p ts
sp-cast-∙idr p ts = ap (λ ρ → sp-cast ρ ts) (∙-idr p)

-- Heterogeneous congruence for sub: apply it under the interval.
sub-pathp : {P : Θ ≡ Θ'} {Q : Ξ ≡ Ξ'} {W : Γ ≡ Γ'} {R : Ρ ≡ Ρ'}
            {s : Split x Θ Ρ Ξ} {s' : Split x Θ' Ρ' Ξ'}
            {t : Tm Ρ z} {t' : Tm Ρ' z} {g : Tm Γ x} {g' : Tm Γ' x}
          → PathP (λ i → Split x (P i) (R i) (Q i)) s s'
          → PathP (λ i → Tm (R i) z) t t'
          → PathP (λ i → Tm (W i) x) g g'
          → PathP (λ i → Tm (P i ++ W i ++ Q i) z) (sub s t g) (sub s' t' g')
sub-pathp S T Gp i = sub (S i) (T i) (Gp i)

sub-sp-pathp : {P : Θ ≡ Θ'} {Q : Ξ ≡ Ξ'} {W : Γ ≡ Γ'} {R : Ρ ≡ Ρ'}
               {s : Split x Θ Ρ Ξ} {s' : Split x Θ' Ρ' Ξ'}
               {ts : Sp Ρ As} {ts' : Sp Ρ' As} {g : Tm Γ x} {g' : Tm Γ' x}
             → PathP (λ i → Split x (P i) (R i) (Q i)) s s'
             → PathP (λ i → Sp (R i) As) ts ts'
             → PathP (λ i → Tm (W i) x) g g'
             → PathP (λ i → Sp (P i ++ W i ++ Q i) As) (sub-sp s ts g) (sub-sp s' ts' g')
sub-sp-pathp S T Gp i = sub-sp (S i) (T i) (Gp i)

-- Mark the slot sitting *behind* another slot: if s₁ marks x in Ρ and s₂
-- marks y inside s₁'s suffix, then y is a slot of Ρ with prefix Θ ++ x ∷ Μ.
-- (The witness needed to state interchange.)
split-behind : Split x Θ Ρ Ξ → Split y Μ Ξ Κ → Split y (Θ ++ x ∷ Μ) Ρ Κ
split-behind here       s₂ = there s₂
split-behind (there s₁) s₂ = there (split-behind s₁ s₂)

-- Reconcile the base of a hom-PathP along an equality of context paths
-- (the analogue of Strictification's hom-over).
tm-over : {p q : Γ ≡ Γ'} (α : p ≡ q) {t : Tm Γ z} {t' : Tm Γ' z}
        → PathP (λ i → Tm (p i) z) t t' → PathP (λ i → Tm (q i) z) t t'
tm-over α {t = t} {t' = t'} = subst (λ p → PathP (λ i → Tm (p i) _) t t') α

sp-over : {p q : Γ ≡ Γ'} (α : p ≡ q) {ts : Sp Γ As} {ts' : Sp Γ' As}
        → PathP (λ i → Sp (p i) As) ts ts' → PathP (λ i → Sp (q i) As) ts ts'
sp-over α {ts = ts} {ts' = ts'} = subst (λ p → PathP (λ i → Sp (p i) _) ts ts') α

split-over : {p q : Θ ≡ Θ'} {r s : Ξ ≡ Ξ'} {u v : Ρ ≡ Ρ'}
             (α : p ≡ q) (β : r ≡ s) (γ : u ≡ v)
             {s₀ : Split x Θ Ρ Ξ} {s₁ : Split x Θ' Ρ' Ξ'}
           → PathP (λ i → Split x (p i) (u i) (r i)) s₀ s₁
           → PathP (λ i → Split x (q i) (v i) (s i)) s₀ s₁
split-over {x = x} α β γ {s₀} {s₁} co =
  transport (λ j → PathP (λ i → Split x (α j i) (γ j i) (β j i)) s₀ s₁) co

-- Paths (and PathPs over context paths) land in the congruence.
≈-of-path : {t t' : Tm Γ z} → t ≡ t' → t ≈ t'
≈-of-path {t = t} p = subst (λ t' → t ≈ t') p ≈-refl

pathp→≈ : {p : Ρ ≡ Γ} {t : Tm Ρ z} {t' : Tm Γ z}
        → PathP (λ i → Tm (p i) z) t t' → cast p t ≈ t'
pathp→≈ {p = p} P = ≈-of-path (from-pathp P)

≈←pathp : {p : Ρ ≡ Γ} {t : Tm Ρ z} {t' : Tm Γ z}
        → PathP (λ i → Tm (p i) z) t t' → t' ≈ cast p t
≈←pathp P = ≈-sym (pathp→≈ P)

-- ==========================================================================
-- One-dimensional path algebra.  Coherences BETWEEN structural boundary
-- paths (so ∙-composites are fine inside them); shared by Identity,
-- Assoc, RedexStability and Freeness.
-- ==========================================================================

-- A square with constant right edge commutes: L ∙ v ≡ u.
square→∙ˡ : ∀ {ℓ} {X : Type ℓ} {a b c : X} {L : a ≡ b} {u : a ≡ c} {v : b ≡ c}
          → PathP (λ k → L k ≡ c) u v → L ∙ v ≡ u
square→∙ˡ {u = u} sq = square→commutes sq ∙ ∙-idr u

-- Move a composite equation to the other side of an inverse.
flip-cancel : ∀ {ℓ} {X : Type ℓ} {a b c : X} (p : a ≡ b) {d : a ≡ c} {e : b ≡ c}
            → p ∙ e ≡ d → sym p ∙ d ≡ e
flip-cancel p θ = ap (sym p ∙_) (sym θ) ∙ ∙-cancell p _

-- Absorb one soundness square into a flatten-style composite: given the
-- co-square of the view (u ⇝ v over the moving edge w) and the δ-lemma
-- for the flatten path F, the whole cast boundary composed with the
-- goal's base path v is the constructor's base path r.
θ-step : ∀ {ℓ} {X : Type ℓ} {a b c d' : X} (F : a ≡ b)
         {w : b ≡ c} {v : c ≡ d'} {u : b ≡ d'} {r : a ≡ d'}
       → PathP (λ k → w k ≡ d') u v
       → F ∙ u ≡ r
       → (F ∙ w) ∙ v ≡ r
θ-step F {w = w} {v = v} sq δ =
  sym (∙-assoc F w v) ∙ ap (F ∙_) (square→∙ˡ sq) ∙ δ

-- Same, absorbing two nested soundness squares (two-level match views).
θ-step₂ : ∀ {ℓ} {X : Type ℓ} {a b c c' d' : X} (F : a ≡ b)
          {w₂ : b ≡ c} {w₁ : c ≡ c'} {v : c' ≡ d'}
          {m₂ : c ≡ d'} {u : b ≡ d'} {r : a ≡ d'}
        → PathP (λ k → w₁ k ≡ d') m₂ v
        → PathP (λ k → w₂ k ≡ d') u m₂
        → F ∙ u ≡ r
        → (F ∙ (w₂ ∙ w₁)) ∙ v ≡ r
θ-step₂ F {w₂ = w₂} {w₁ = w₁} {v = v} sq₁ sq₂ δ =
  sym (∙-assoc F (w₂ ∙ w₁) v)
  ∙ ap (F ∙_) (sym (∙-assoc w₂ w₁ v) ∙ ap (w₂ ∙_) (square→∙ˡ sq₁) ∙ square→∙ˡ sq₂)
  ∙ δ

-- ap distributes over a composite (1lab's ap-∙, flipped).
∙-ap₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {v w x' : X}
        (p : v ≡ w) (q : w ≡ x')
      → ap f p ∙ ap f q ≡ ap f (p ∙ q)
∙-ap₂ f p q = sym (ap-∙ f p q)

-- Push a composite equation under an ap (the cons step of every δ-lemma).
-- p, q, r are implicit so the recursive call's type pins them.
ap-∙-step : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c : X}
            {p : a ≡ b} {q : b ≡ c} {r : a ≡ c}
          → p ∙ q ≡ r → ap f p ∙ ap f q ≡ ap f r
ap-∙-step f {p = p} {q = q} eq = sym (ap-∙ f p q) ∙ ap (ap f) eq

-- The diagonal of a two-parameter family is the composite of its edges.
diag-∙ : ∀ {ℓa ℓb ℓc} {X : Type ℓa} {Y : Type ℓb} {Z : Type ℓc}
         (f : X → Y → Z) {a a' : X} {b b' : Y} (q : a ≡ a') (p : b ≡ b')
       → (λ i → f (q i) (p i)) ≡ (λ i → f a (p i)) ∙ (λ i → f (q i) b')
diag-∙ f q p = ∙-unique _ λ i j → f (q (i ∧ j)) (p j)
