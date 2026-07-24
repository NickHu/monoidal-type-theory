open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory.Free

module Multicategory.Free.CongruenceRight {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G
open import Multicategory.Free.RedexStability G

-- Substitution respects the β/η-congruence in its target (left-hand)
-- argument: t ≈ t' ⟹ t[g/x] ≈ t'[g/x], mutually with spines, by induction
-- on the congruence derivation.  The congruence cases mirror sub's call
-- graph (one lemma per branch handler, matching the Split-++ view, exactly
-- as in CongruenceLeft); the β/η cases are the standalone redex-stability
-- lemmas — they use no induction hypothesis.

private module G = Multigraph G

private variable
  x z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Γ₁ Δ₁ Γm Δm Θ₂ : Ctx
  As : List G.Ob

-- The spine analogue of Kit's cast-≈.
private
  sp-cast-≈ₛ : {ts ts' : Sp Ρ As} (p : Ρ ≡ Γ)
             → ts ≈ₛ ts' → sp-cast p ts ≈ₛ sp-cast p ts'
  sp-cast-≈ₛ {ts = ts} {ts' = ts'} p e =
    transport (λ i → sp-cast-filler p ts i ≈ₛ sp-cast-filler p ts' i) e

-- ==========================================================================
-- The mutual induction on the congruence derivation.
-- ==========================================================================

sub-≈ʳ    : (s : Split x Θ Ρ Ξ) {t t' : Tm Ρ z}
          → t ≈ t' → (g : Tm Γ x) → sub s t g ≈ sub s t' g
sub-sp-≈ʳ : (s : Split x Θ Ρ Ξ) {ts ts' : Sp Ρ As}
          → ts ≈ₛ ts' → (g : Tm Γ x) → sub-sp s ts g ≈ₛ sub-sp s ts' g

sub-pair-≈ʳ : {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
              {M M' : Tm Γ₁ A} {N N' : Tm Δ₁ B}
            → M ≈ M' → N ≈ N' → (g : Tm Γ x)
            → sub-pair v M N g ≈ sub-pair v M' N' g

sub-match⊗ˡ-≈ʳ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
                 {M M' : Tm Ψ (A ⊗ B)} {N N' : Tm (Γm ++ A ∷ B ∷ Δm) C}
               → M ≈ M' → N ≈ N' → (g : Tm Γ x)
               → sub-match⊗ˡ v M N g ≈ sub-match⊗ˡ v M' N' g
sub-match⊗ʳ-≈ʳ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s')
                 (q : Γm ++ Θ₂ ≡ Θ)
                 {M M' : Tm Ψ (A ⊗ B)} {N N' : Tm (Γm ++ A ∷ B ∷ Δm) C}
               → M ≈ M' → N ≈ N' → (g : Tm Γ x)
               → sub-match⊗ʳ v q M N g ≈ sub-match⊗ʳ v q M' N' g

sub-match𝟙ˡ-≈ʳ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
                 {M M' : Tm Ψ 𝟙} {N N' : Tm (Γm ++ Δm) C}
               → M ≈ M' → N ≈ N' → (g : Tm Γ x)
               → sub-match𝟙ˡ v M N g ≈ sub-match𝟙ˡ v M' N' g
sub-match𝟙ʳ-≈ʳ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s')
                 (q : Γm ++ Θ₂ ≡ Θ)
                 {M M' : Tm Ψ 𝟙} {N N' : Tm (Γm ++ Δm) C}
               → M ≈ M' → N ≈ N' → (g : Tm Γ x)
               → sub-match𝟙ʳ v q M N g ≈ sub-match𝟙ʳ v q M' N' g

sub-cons-≈ʳ : ∀ {A : G.Ob} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
              {t t' : Tm Γ₁ (base A)} {ts ts' : Sp Δ₁ As}
            → t ≈ t' → ts ≈ₛ ts' → (g : Tm Γ x)
            → sub-cons v t ts g ≈ₛ sub-cons v t' ts' g

sub-≈ʳ s ≈-refl                       g = ≈-refl
sub-≈ʳ s (≈-sym e)                    g = ≈-sym (sub-≈ʳ s e g)
sub-≈ʳ s (≈-trans e₁ e₂)              g = ≈-trans (sub-≈ʳ s e₁ g) (sub-≈ʳ s e₂ g)
sub-≈ʳ s (gen-cong es)                g = gen-cong (sub-sp-≈ʳ s es g)
sub-≈ʳ s (⦅,⦆-cong {Γ = Γ₁} e₁ e₂)    g = sub-pair-≈ʳ (split-++ Γ₁ s) e₁ e₂ g
sub-≈ʳ s (match⊗-cong {Γ = Γm} e₁ e₂) g = sub-match⊗ˡ-≈ʳ (split-++ Γm s) e₁ e₂ g
sub-≈ʳ s (match𝟙-cong {Γ = Γm} e₁ e₂) g = sub-match𝟙ˡ-≈ʳ (split-++ Γm s) e₁ e₂ g
sub-≈ʳ s (β⊗ {Γm = Γm} {Δm = Δm} M N P)  g = β⊗-sub {Γm = Γm} {Δm = Δm} s M N P g
sub-≈ʳ s (η⊗ {Γm = Γm} {Δm = Δm} M N)    g = η⊗-sub {Γm = Γm} {Δm = Δm} s M N g
sub-≈ʳ s (β𝟙 {Γm = Γm} {Δm = Δm} N)      g = β𝟙-sub {Γm = Γm} {Δm = Δm} s N g
sub-≈ʳ s (η𝟙 {Γm = Γm} {Δm = Δm} M N)    g = η𝟙-sub {Γm = Γm} {Δm = Δm} s M N g

sub-sp-≈ʳ s nil                  g = absurd (split-[] s)
sub-sp-≈ʳ s (cons {Γ = Γ₁} e es) g = sub-cons-≈ʳ (split-++ Γ₁ s) e es g

sub-pair-≈ʳ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) e₁ e₂ g =
  cast-≈ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (⦅,⦆-cong (sub-≈ʳ s₁ e₁ g) e₂)
sub-pair-≈ʳ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) e₁ e₂ g =
  cast-≈ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (⦅,⦆-cong e₁ (sub-≈ʳ s₂ e₂ g))

sub-match⊗ˡ-≈ʳ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {A = A} {B = B} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) e₁ e₂ g =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match⊗-cong e₁
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
        (sub-≈ʳ (split-++ˡ s₁ (A ∷ B ∷ Δm)) e₂ g)))
sub-match⊗ˡ-≈ʳ {Ψ = Ψ} (on-right s' q _) e₁ e₂ g =
  sub-match⊗ʳ-≈ʳ (split-++ Ψ s') q e₁ e₂ g

sub-match⊗ʳ-≈ʳ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q e₁ e₂ g =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match⊗-cong (sub-≈ʳ s₁ e₁ g) e₂)
sub-match⊗ʳ-≈ʳ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {A = A} {B = B} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q e₁ e₂ g =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match⊗-cong e₁
      (cast-≈ (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
        (sub-≈ʳ (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) e₂ g)))

sub-match𝟙ˡ-≈ʳ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) e₁ e₂ g =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match𝟙-cong {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} e₁
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ Δm))
        (sub-≈ʳ (split-++ˡ s₁ Δm) e₂ g)))
sub-match𝟙ˡ-≈ʳ {Ψ = Ψ} (on-right s' q _) e₁ e₂ g =
  sub-match𝟙ʳ-≈ʳ (split-++ Ψ s') q e₁ e₂ g

sub-match𝟙ʳ-≈ʳ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q e₁ e₂ g =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match𝟙-cong {Γ = Γm} {Δ = Δm} (sub-≈ʳ s₁ e₁ g) e₂)
sub-match𝟙ʳ-≈ʳ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q e₁ e₂ g =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match𝟙-cong {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} e₁
      (cast-≈ (sym (flattenʳ Γm Θ₃ Γ Ξ))
        (sub-≈ʳ (split-++ʳ Γm s₂) e₂ g)))

sub-cons-≈ʳ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) e es g =
  sp-cast-≈ₛ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (cons (sub-≈ʳ s₁ e g) es)
sub-cons-≈ʳ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) e es g =
  sp-cast-≈ₛ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (cons e (sub-sp-≈ʳ s₂ es g))
