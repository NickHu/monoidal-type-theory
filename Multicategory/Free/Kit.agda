open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
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
