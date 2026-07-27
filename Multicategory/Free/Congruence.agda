open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List

open import Multicategory.Free

module Multicategory.Free.Congruence {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G
open import Multicategory.Free.RedexStability G

-- Substitution respects the β/η-congruence in both arguments:
--   sub-≈ˡ :  g ≈ g'  ⟹  t[g/x] ≈ t[g'/x]   (induction on the term)
--   sub-≈ʳ :  t ≈ t'  ⟹  t[g/x] ≈ t'[g/x]   (induction on the derivation,
--                                             β/η cases from RedexStability)
-- Both proofs share ONE handler layer, stated two-sidedly: each branch
-- handler of sub sends componentwise-related inputs over possibly different
-- substituends to related outputs,
--   sub-pair v M N g ≈ sub-pair v M' N' g',
-- taking the recursive congruences on the components as continuations (so
-- the handlers are non-recursive and each top level keeps its own
-- termination measure).  The two inductions differ only in how they
-- instantiate the continuations: sub-≈ˡ pins the term side with ≈-refl and
-- recurses on subterms; sub-≈ʳ pins the substituend and recurses on
-- subderivations.

private module G = Multigraph G

private variable
  x z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Γ₁ Δ₁ Γm Δm Θ₂ : Ctx
  As : List G.Ob

-- Reflexivity of the spine congruence, cons-by-cons.  (The spine analogue
-- of cast-≈, sp-cast-≈ₛ, comes from Kit.)
≈ₛ-refl : (ts : Sp Γ As) → ts ≈ₛ ts
≈ₛ-refl []       = nil
≈ₛ-refl (t ∷ ts) = cons ≈-refl (≈ₛ-refl ts)

-- ==========================================================================
-- The shared, two-sided handler layer: one lemma per branch handler of sub,
-- matching the Split-++ view, so every clause's goal reduces definitionally
-- to a cast of a constructor, discharged by cast-≈ (resp. sp-cast-≈ₛ)
-- around the constructor's congruence rule.
-- ==========================================================================

sub-var-≈ : (s : Split x Θ (z ∷ []) Ξ) {g g' : Tm Γ x}
          → g ≈ g' → sub-var s g ≈ sub-var s g'
sub-var-≈ {Γ = Γ} here e = cast-≈ (sym (++-idr Γ)) e
sub-var-≈ (there s)    e = absurd (split-[] s)

sub-pair-≈
  : {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
    {M M' : Tm Γ₁ A} {N N' : Tm Δ₁ B} {g g' : Tm Γ x}
  → M ≈ M' → N ≈ N'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Γ₁ Ξ') → sub s₁ M g ≈ sub s₁ M' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' Δ₁ Ξ') → sub s₂ N g ≈ sub s₂ N' g')
  → sub-pair v M N g ≈ sub-pair v M' N' g'
sub-pair-≈ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) eM eN recM recN =
  cast-≈ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (⦅,⦆-cong (recM s₁) eN)
sub-pair-≈ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) eM eN recM recN =
  cast-≈ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (⦅,⦆-cong eM (recN s₂))

sub-match⊗ʳ-≈
  : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
    {M M' : Tm Ψ (A ⊗ B)} {N N' : Tm (Γm ++ A ∷ B ∷ Δm) C} {g g' : Tm Γ x}
  → M ≈ M' → N ≈ N'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Ψ Ξ') → sub s₁ M g ≈ sub s₁ M' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' (Γm ++ A ∷ B ∷ Δm) Ξ') → sub s₂ N g ≈ sub s₂ N' g')
  → sub-match⊗ʳ v q M N g ≈ sub-match⊗ʳ v q M' N' g'
sub-match⊗ʳ-≈ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q eM eN recM recN =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match⊗-cong (recM s₁) eN)
sub-match⊗ʳ-≈ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {A = A} {B = B} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q eM eN recM recN =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match⊗-cong eM
      (cast-≈ (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
        (recN (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)))))

sub-match⊗ˡ-≈
  : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
    {M M' : Tm Ψ (A ⊗ B)} {N N' : Tm (Γm ++ A ∷ B ∷ Δm) C} {g g' : Tm Γ x}
  → M ≈ M' → N ≈ N'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Ψ Ξ') → sub s₁ M g ≈ sub s₁ M' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' (Γm ++ A ∷ B ∷ Δm) Ξ') → sub s₂ N g ≈ sub s₂ N' g')
  → sub-match⊗ˡ v M N g ≈ sub-match⊗ˡ v M' N' g'
sub-match⊗ˡ-≈ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {A = A} {B = B} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) eM eN recM recN =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match⊗-cong eM
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
        (recN (split-++ˡ s₁ (A ∷ B ∷ Δm)))))
sub-match⊗ˡ-≈ {Ψ = Ψ} (on-right s' q _) eM eN recM recN =
  sub-match⊗ʳ-≈ (split-++ Ψ s') q eM eN recM recN

sub-match𝟙ʳ-≈
  : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
    {M M' : Tm Ψ 𝟙} {N N' : Tm (Γm ++ Δm) C} {g g' : Tm Γ x}
  → M ≈ M' → N ≈ N'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Ψ Ξ') → sub s₁ M g ≈ sub s₁ M' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' (Γm ++ Δm) Ξ') → sub s₂ N g ≈ sub s₂ N' g')
  → sub-match𝟙ʳ v q M N g ≈ sub-match𝟙ʳ v q M' N' g'
sub-match𝟙ʳ-≈ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q eM eN recM recN =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match𝟙-cong {Γ = Γm} {Δ = Δm} (recM s₁) eN)
sub-match𝟙ʳ-≈ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q eM eN recM recN =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match𝟙-cong {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} eM
      (cast-≈ (sym (flattenʳ Γm Θ₃ Γ Ξ))
        (recN (split-++ʳ Γm s₂))))

sub-match𝟙ˡ-≈
  : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
    {M M' : Tm Ψ 𝟙} {N N' : Tm (Γm ++ Δm) C} {g g' : Tm Γ x}
  → M ≈ M' → N ≈ N'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Ψ Ξ') → sub s₁ M g ≈ sub s₁ M' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' (Γm ++ Δm) Ξ') → sub s₂ N g ≈ sub s₂ N' g')
  → sub-match𝟙ˡ v M N g ≈ sub-match𝟙ˡ v M' N' g'
sub-match𝟙ˡ-≈ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) eM eN recM recN =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match𝟙-cong {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} eM
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ Δm))
        (recN (split-++ˡ s₁ Δm))))
sub-match𝟙ˡ-≈ {Ψ = Ψ} (on-right s' q _) eM eN recM recN =
  sub-match𝟙ʳ-≈ (split-++ Ψ s') q eM eN recM recN

sub-cons-≈
  : ∀ {A : G.Ob} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
    {t t' : Tm Γ₁ (base A)} {ts ts' : Sp Δ₁ As} {g g' : Tm Γ x}
  → t ≈ t' → ts ≈ₛ ts'
  → (∀ {Θ' Ξ'} (s₁ : Split x Θ' Γ₁ Ξ') → sub s₁ t g ≈ sub s₁ t' g')
  → (∀ {Θ' Ξ'} (s₂ : Split x Θ' Δ₁ Ξ') → sub-sp s₂ ts g ≈ₛ sub-sp s₂ ts' g')
  → sub-cons v t ts g ≈ₛ sub-cons v t' ts' g'
sub-cons-≈ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) et ets rect rects =
  sp-cast-≈ₛ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (cons (rect s₁) ets)
sub-cons-≈ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) et ets rect rects =
  sp-cast-≈ₛ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (cons et (rects s₂))

-- ==========================================================================
-- Congruence in the substituted argument: induction on the term.
-- ==========================================================================

sub-≈ˡ    : (s : Split x Θ Ρ Ξ) (t : Tm Ρ z) {g g' : Tm Γ x}
          → g ≈ g' → sub s t g ≈ sub s t g'
sub-sp-≈ˡ : (s : Split x Θ Ρ Ξ) (ts : Sp Ρ As) {g g' : Tm Γ x}
          → g ≈ g' → sub-sp s ts g ≈ₛ sub-sp s ts g'

sub-≈ˡ s var                  e = sub-var-≈ s e
sub-≈ˡ s (gen f sp)           e = gen-cong (sub-sp-≈ˡ s sp e)
sub-≈ˡ s (⦅_,_⦆ {Γ = Γ₁} P Q) e =
  sub-pair-≈ (split-++ Γ₁ s) (≈-refl {t = P}) (≈-refl {t = Q})
    (λ s₁ → sub-≈ˡ s₁ P e) (λ s₂ → sub-≈ˡ s₂ Q e)
sub-≈ˡ s (match⊗ {Γ = Γm} P Q) e =
  sub-match⊗ˡ-≈ (split-++ Γm s) (≈-refl {t = P}) (≈-refl {t = Q})
    (λ s₁ → sub-≈ˡ s₁ P e) (λ s₂ → sub-≈ˡ s₂ Q e)
sub-≈ˡ s ⋆                    e = absurd (split-[] s)
sub-≈ˡ s (match𝟙 {Γ = Γm} P Q) e =
  sub-match𝟙ˡ-≈ (split-++ Γm s) (≈-refl {t = P}) (≈-refl {t = Q})
    (λ s₁ → sub-≈ˡ s₁ P e) (λ s₂ → sub-≈ˡ s₂ Q e)

sub-sp-≈ˡ s []                  e = absurd (split-[] s)
sub-sp-≈ˡ s (_∷_ {Γ = Γ₁} t ts) e =
  sub-cons-≈ (split-++ Γ₁ s) (≈-refl {t = t}) (≈ₛ-refl ts)
    (λ s₁ → sub-≈ˡ s₁ t e) (λ s₂ → sub-sp-≈ˡ s₂ ts e)

-- ==========================================================================
-- Congruence in the target: induction on the derivation; the β/η cases are
-- the standalone redex-stability lemmas (no induction hypothesis).
-- ==========================================================================

sub-≈ʳ    : (s : Split x Θ Ρ Ξ) {t t' : Tm Ρ z}
          → t ≈ t' → (g : Tm Γ x) → sub s t g ≈ sub s t' g
sub-sp-≈ʳ : (s : Split x Θ Ρ Ξ) {ts ts' : Sp Ρ As}
          → ts ≈ₛ ts' → (g : Tm Γ x) → sub-sp s ts g ≈ₛ sub-sp s ts' g

sub-≈ʳ s ≈-refl                       g = ≈-refl
sub-≈ʳ s (≈-sym e)                    g = ≈-sym (sub-≈ʳ s e g)
sub-≈ʳ s (≈-trans e₁ e₂)              g = ≈-trans (sub-≈ʳ s e₁ g) (sub-≈ʳ s e₂ g)
sub-≈ʳ s (gen-cong es)                g = gen-cong (sub-sp-≈ʳ s es g)
sub-≈ʳ s (⦅,⦆-cong {Γ = Γ₁} e₁ e₂)    g =
  sub-pair-≈ (split-++ Γ₁ s) e₁ e₂
    (λ s₁ → sub-≈ʳ s₁ e₁ g) (λ s₂ → sub-≈ʳ s₂ e₂ g)
sub-≈ʳ s (match⊗-cong {Γ = Γm} e₁ e₂) g =
  sub-match⊗ˡ-≈ (split-++ Γm s) e₁ e₂
    (λ s₁ → sub-≈ʳ s₁ e₁ g) (λ s₂ → sub-≈ʳ s₂ e₂ g)
sub-≈ʳ s (match𝟙-cong {Γ = Γm} e₁ e₂) g =
  sub-match𝟙ˡ-≈ (split-++ Γm s) e₁ e₂
    (λ s₁ → sub-≈ʳ s₁ e₁ g) (λ s₂ → sub-≈ʳ s₂ e₂ g)
sub-≈ʳ s (β⊗ {Γm = Γm} {Δm = Δm} M N P)  g = β⊗-sub {Γm = Γm} {Δm = Δm} s M N P g
sub-≈ʳ s (η⊗ {Γm = Γm} {Δm = Δm} M N)    g = η⊗-sub {Γm = Γm} {Δm = Δm} s M N g
sub-≈ʳ s (β𝟙 {Γm = Γm} {Δm = Δm} N)      g = β𝟙-sub {Γm = Γm} {Δm = Δm} s N g
sub-≈ʳ s (η𝟙 {Γm = Γm} {Δm = Δm} M N)    g = η𝟙-sub {Γm = Γm} {Δm = Δm} s M N g

sub-sp-≈ʳ s nil                  g = absurd (split-[] s)
sub-sp-≈ʳ s (cons {Γ = Γ₁} e es) g =
  sub-cons-≈ (split-++ Γ₁ s) e es
    (λ s₁ → sub-≈ʳ s₁ e g) (λ s₂ → sub-sp-≈ʳ s₂ es g)
