open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory.Free

module Multicategory.Free.CongruenceLeft {o h} (G : Multigraph o h) where

open import Multicategory.Free.Kit G

-- Substitution respects the β/η-congruence in its substituted (right-hand)
-- argument: g ≈ g' ⟹ t[g/x] ≈ t[g'/x], mutually with spines.  The proof
-- mirrors sub's own call graph exactly — one lemma per branch handler,
-- matching the Split-++ view — so every clause's goal reduces definitionally
-- to a cast of a constructor, discharged by cast-≈ (resp. the spine analogue
-- sp-cast-≈ₛ below) around the constructor's congruence rule with the IH in
-- the active position and reflexivity elsewhere.

private module G = Multigraph G

private variable
  x z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Γ₁ Δ₁ Γm Δm Θ₂ : Ctx
  As : List G.Ob

-- Reflexivity of the spine congruence, cons-by-cons.  (The spine analogue
-- of cast-≈, sp-cast-≈ₛ, comes from Kit.)
private
  ≈ₛ-refl : (ts : Sp Γ As) → ts ≈ₛ ts
  ≈ₛ-refl []       = nil
  ≈ₛ-refl (t ∷ ts) = cons ≈-refl (≈ₛ-refl ts)

-- ==========================================================================
-- The mutual induction, one lemma per branch handler of sub.
-- ==========================================================================

sub-≈ˡ    : (s : Split x Θ Ρ Ξ) (t : Tm Ρ z) {g g' : Tm Γ x}
          → g ≈ g' → sub s t g ≈ sub s t g'
sub-sp-≈ˡ : (s : Split x Θ Ρ Ξ) (ts : Sp Ρ As) {g g' : Tm Γ x}
          → g ≈ g' → sub-sp s ts g ≈ₛ sub-sp s ts g'

sub-var-≈ˡ : (s : Split x Θ (z ∷ []) Ξ) {g g' : Tm Γ x}
           → g ≈ g' → sub-var s g ≈ sub-var s g'

sub-pair-≈ˡ : {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
              (P : Tm Γ₁ A) (Q : Tm Δ₁ B) {g g' : Tm Γ x}
            → g ≈ g' → sub-pair v P Q g ≈ sub-pair v P Q g'

sub-match⊗ˡ-≈ˡ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
                 (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) {g g' : Tm Γ x}
               → g ≈ g' → sub-match⊗ˡ v P Q g ≈ sub-match⊗ˡ v P Q g'
sub-match⊗ʳ-≈ˡ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s')
                 (q : Γm ++ Θ₂ ≡ Θ)
                 (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) {g g' : Tm Γ x}
               → g ≈ g' → sub-match⊗ʳ v q P Q g ≈ sub-match⊗ʳ v q P Q g'

sub-match𝟙ˡ-≈ˡ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} (v : Split-++ Γm (Ψ ++ Δm) s)
                 (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) {g g' : Tm Γ x}
               → g ≈ g' → sub-match𝟙ˡ v P Q g ≈ sub-match𝟙ˡ v P Q g'
sub-match𝟙ʳ-≈ˡ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} (v : Split-++ Ψ Δm s')
                 (q : Γm ++ Θ₂ ≡ Θ)
                 (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) {g g' : Tm Γ x}
               → g ≈ g' → sub-match𝟙ʳ v q P Q g ≈ sub-match𝟙ʳ v q P Q g'

sub-cons-≈ˡ : ∀ {A : G.Ob} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
              (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) {g g' : Tm Γ x}
            → g ≈ g' → sub-cons v t ts g ≈ₛ sub-cons v t ts g'

sub-≈ˡ s var                  e = sub-var-≈ˡ s e
sub-≈ˡ s (gen f sp)           e = gen-cong (sub-sp-≈ˡ s sp e)
sub-≈ˡ s (⦅_,_⦆ {Γ = Γ₁} P Q) e = sub-pair-≈ˡ (split-++ Γ₁ s) P Q e
sub-≈ˡ s (match⊗ {Γ = Γm} P Q) e = sub-match⊗ˡ-≈ˡ (split-++ Γm s) P Q e
sub-≈ˡ s ⋆                    e = absurd (split-[] s)
sub-≈ˡ s (match𝟙 {Γ = Γm} P Q) e = sub-match𝟙ˡ-≈ˡ (split-++ Γm s) P Q e

sub-sp-≈ˡ s []                  e = absurd (split-[] s)
sub-sp-≈ˡ s (_∷_ {Γ = Γ₁} t ts) e = sub-cons-≈ˡ (split-++ Γ₁ s) t ts e

sub-var-≈ˡ {Γ = Γ} here e = cast-≈ (sym (++-idr Γ)) e
sub-var-≈ˡ (there s)    e = absurd (split-[] s)

sub-pair-≈ˡ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q e =
  cast-≈ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (⦅,⦆-cong (sub-≈ˡ s₁ P e) (≈-refl {t = Q}))
sub-pair-≈ˡ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) P Q e =
  cast-≈ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (⦅,⦆-cong (≈-refl {t = P}) (sub-≈ˡ s₂ Q e))

sub-match⊗ˡ-≈ˡ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {A = A} {B = B} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q e =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match⊗-cong (≈-refl {t = P})
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
        (sub-≈ˡ (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q e)))
sub-match⊗ˡ-≈ˡ {Ψ = Ψ} (on-right s' q _) P Q e =
  sub-match⊗ʳ-≈ˡ (split-++ Ψ s') q P Q e

sub-match⊗ʳ-≈ˡ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q P Q e =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match⊗-cong (sub-≈ˡ s₁ P e) (≈-refl {t = Q}))
sub-match⊗ʳ-≈ˡ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {A = A} {B = B} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q P Q e =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match⊗-cong (≈-refl {t = P})
      (cast-≈ (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
        (sub-≈ˡ (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q e)))

sub-match𝟙ˡ-≈ˡ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q e =
  cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (match𝟙-cong {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} (≈-refl {t = P})
      (cast-≈ (sym (flattenˡ Θ Γ Ξ₁ Δm))
        (sub-≈ˡ (split-++ˡ s₁ Δm) Q e)))
sub-match𝟙ˡ-≈ˡ {Ψ = Ψ} (on-right s' q _) P Q e =
  sub-match𝟙ʳ-≈ˡ (split-++ Ψ s') q P Q e

sub-match𝟙ʳ-≈ˡ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
  (on-left {Ξ₁ = Ξ₁} s₁ p _) q P Q e =
  cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
    (match𝟙-cong {Γ = Γm} {Δ = Δm} (sub-≈ˡ s₁ P e) (≈-refl {t = Q}))
sub-match𝟙ʳ-≈ˡ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {Γ = Γ}
  (on-right {Θ₂ = Θ₃} s₂ q₂ _) q P Q e =
  cast-≈ (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (match𝟙-cong {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} (≈-refl {t = P})
      (cast-≈ (sym (flattenʳ Γm Θ₃ Γ Ξ))
        (sub-≈ˡ (split-++ʳ Γm s₂) Q e)))

sub-cons-≈ˡ {Θ = Θ} {Δ₁ = Δ₁} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) t ts e =
  sp-cast-≈ₛ (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
    (cons (sub-≈ˡ s₁ t e) (≈ₛ-refl ts))
sub-cons-≈ˡ {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) t ts e =
  sp-cast-≈ₛ (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
    (cons (≈-refl {t = t}) (sub-sp-≈ˡ s₂ ts e))
