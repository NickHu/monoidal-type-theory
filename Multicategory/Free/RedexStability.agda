open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
open import Multicategory.Free

module Multicategory.Free.RedexStability {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G
open import ListPath.Solver using (list!)
open import Multicategory.Free.Identity G
open import Multicategory.Free.Assoc G
open import Multicategory.Free.Interchange G

-- The four β/η reduction rules are stable under an ambient substitution
-- sub s - g: the standalone content of the β/η cases of right congruence
-- (no induction hypothesis).  Each proof cases on the view(s) of s,
-- reduces the LHS through sub's handlers, fires the rule at the
-- substituted configuration via cast-≈, and reconciles with the RHS by
-- sub-id / sub-assoc / sub-interchange converted through pathp→≈.

private variable
  x z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Γ₁ Δ₁ Ξ₁ Γm Δm Ψm Θ₂ : Ctx

-- ==========================================================================
-- β𝟙: match𝟙(⋆, N)[g/x] ≈ N[g/x].
-- ==========================================================================

private
  -- bury with empty middle is flattenʳ (both structural; base case is
  -- sym refl vs refl, which agree definitionally).
  bury-nil : ∀ (Γm Θ₂ Γ Ξ : Ctx)
           → bury Γm [] Θ₂ (Γ ++ Ξ) ≡ flattenʳ Γm Θ₂ Γ Ξ
  bury-nil []       Θ₂ Γ Ξ = refl
  bury-nil (a ∷ Γm) Θ₂ Γ Ξ = ap (ap (a ∷_)) (bury-nil Γm Θ₂ Γ Ξ)

  β𝟙-sub-handler : ∀ {x C : Ty} {Θ Γm Δm Ξ Γ : Ctx} {s : Split x Θ (Γm ++ Δm) Ξ}
      (v : Split-++ Γm Δm s) (N : Tm (Γm ++ Δm) C) (g : Tm Γ x)
    → sub-match𝟙ˡ {Ψ = []} v ⋆ N g ≈ sub s N g
  β𝟙-sub-handler {x = x} {C = C} {Θ = Θ} {Δm = Δm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p co) N g =
    ≈-trans
      (cast-≈ (flattenˡ Θ Γ Ξ₁ Δm ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
        (β𝟙 {Γm = Θ ++ Γ ++ Ξ₁} {Δm = Δm}
          (cast (sym (flattenˡ Θ Γ Ξ₁ Δm)) (sub (split-++ˡ s₁ Δm) N g))))
      (pathp→≈
        (_∙P_ {B = λ Ρ' → Tm Ρ' C}
              {p = flattenˡ Θ Γ Ξ₁ Δm} {q = ap (λ Ξ' → Θ ++ Γ ++ Ξ') p}
          (symP (cast-filler (sym (flattenˡ Θ Γ Ξ₁ Δm))
            (sub (split-++ˡ s₁ Δm) N g)))
          (sub-pathp {t = N} {t' = N} {g = g} {g' = g} co refl refl)))
  β𝟙-sub-handler {x = x} {C = C} {Θ = Θ} {Γm = Γm} {Δm = Δm} {Ξ = Ξ} {Γ = Γ}
    (on-right {Θ₂ = Θ₂} s₂ q co) N g =
    ≈-trans
      (cast-≈ (bury Γm [] Θ₂ (Γ ++ Ξ)
               ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) refl ∙ q))
        (β𝟙 {Γm = Γm} {Δm = Θ₂ ++ Γ ++ Ξ}
          (cast (sym (flattenʳ Γm Θ₂ Γ Ξ)) (sub (split-++ʳ Γm s₂) N g))))
      (pathp→≈
        (tm-over
          (λ j → bury-nil Γm Θ₂ Γ Ξ (~ j)
               ∙ ap (_++ Γ ++ Ξ) (∙-idl q (~ j)))
          (_∙P_ {B = λ Ρ' → Tm Ρ' C}
                {p = flattenʳ Γm Θ₂ Γ Ξ} {q = ap (_++ Γ ++ Ξ) q}
            (symP (cast-filler (sym (flattenʳ Γm Θ₂ Γ Ξ))
              (sub (split-++ʳ Γm s₂) N g)))
            (sub-pathp {t = N} {t' = N} {g = g} {g' = g} co refl refl))))

β𝟙-sub : ∀ {x C : Ty} {Θ Ξ Γ Γm Δm : Ctx} (s : Split x Θ (Γm ++ Δm) Ξ)
         (N : Tm (Γm ++ Δm) C) (g : Tm Γ x)
       → sub s (match𝟙 {Ψ = []} {Γ = Γm} {Δ = Δm} ⋆ N) g ≈ sub s N g
β𝟙-sub {Γm = Γm} s N g = β𝟙-sub-handler (split-++ Γm s) N g

-- ==========================================================================
-- Shared helpers for the η/β⊗ lemmas: reconciliation of canonical splits
-- with the weakenings sub-interchange/sub-assoc produce, and coherences
-- between the reassociation paths of sub's handlers and the law boundaries
-- (the one-dimensional path algebra ap-∙-step / diag-∙ comes from Kit).
-- ==========================================================================

private
  -- Every split is the canonical one, over its own witnessed path.
  split-canon : ∀ {x : Ty} {Θ Ρ Ξ : Ctx} (s : Split x Θ Ρ Ξ)
              → PathP (λ i → Split x Θ (split-path s i) Ξ) (split-here Θ x Ξ) s
  split-canon here        = refl
  split-canon (there s) i = there (split-canon s i)

  -- split-behind of a suffix-weakened split against the canonical inner
  -- split is the canonical split, over the outer split's path.
  behind-here : ∀ {x y : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (Δm : Ctx)
              → PathP (λ i → Split y (split-path s₁ i) (Γm ++ y ∷ Δm) Δm)
                      (split-behind (split-++ˡ s₁ (y ∷ Δm)) (split-here Ξ₁ y Δm))
                      (split-here Γm y Δm)
  behind-here here       Δm = refl
  behind-here (there s₁) Δm i = there (behind-here s₁ Δm i)

  -- flattenˡ as a composite of the two reassociations it fuses.
  flattenˡ-∙ : ∀ (Θ Γ Ξ₁ Δ' : Ctx)
             → ++-assoc Θ (Γ ++ Ξ₁) Δ' ∙ ap (Θ ++_) (++-assoc Γ Ξ₁ Δ')
             ≡ flattenˡ Θ Γ Ξ₁ Δ'
  flattenˡ-∙ Θ Γ Ξ₁ Δ' = list!

  -- The interchange boundary against flattenˡ / flattenʳ / bury, and the
  -- associativity boundary against flattenᵐ (each cons-by-cons, so the
  -- base cases agree definitionally).
  int-flatˡ : ∀ (Θ Γ Ξ₁ Δh Δm : Ctx)
            → interchangeₘ-boundary Θ Γ Ξ₁ Δh Δm ≡ flattenˡ Θ Γ Ξ₁ (Δh ++ Δm)
  int-flatˡ Θ Γ Ξ₁ Δh Δm = refl -- definitional after the solver aliasing

  int-flatʳ : ∀ (Γm Θ₃ Γ Ξ : Ctx)
            → interchangeₘ-boundary Γm [] Θ₃ Γ Ξ ≡ sym (flattenʳ Γm Θ₃ Γ Ξ)
  int-flatʳ []       Θ₃ Γ Ξ = refl
  int-flatʳ (a ∷ Γm) Θ₃ Γ Ξ = ap (ap (a ∷_)) (int-flatʳ Γm Θ₃ Γ Ξ)

  int-flatʳ₂ : ∀ (Γm Θ₃ Γ Ξ : Ctx) {A B : Ty}
             → interchangeₘ-boundary Γm (A ∷ B ∷ []) Θ₃ Γ Ξ
             ≡ sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ)
  int-flatʳ₂ []       Θ₃ Γ Ξ = refl
  int-flatʳ₂ (a ∷ Γm) Θ₃ Γ Ξ = ap (ap (a ∷_)) (int-flatʳ₂ Γm Θ₃ Γ Ξ)

  int-bury : ∀ (Γm Ψm Θ₃ Γ Ξ : Ctx)
           → sym (interchangeₘ-boundary Γm Ψm Θ₃ Γ Ξ) ≡ bury Γm Ψm Θ₃ (Γ ++ Ξ)
  int-bury Γm Ψm Θ₃ Γ Ξ = list!

  flatˡ-symₐ : ∀ (Θ₂ Γ Ξ₁ Δm : Ctx)
             → sym (assocₘ-flatten Θ₂ Γ Ξ₁ Δm) ≡ flattenˡ Θ₂ Γ Ξ₁ Δm
  flatˡ-symₐ Θ₂ Γ Ξ₁ Δm = list!

  flatᵐ-sym : ∀ (Γm Θ₂ Γ Ξ₁ Δm : Ctx)
            → sym (assocₘ-boundary Γm Θ₂ Γ Ξ₁ Δm) ≡ flattenᵐ Γm Θ₂ Γ Ξ₁ Δm
  flatᵐ-sym Γm Θ₂ Γ Ξ₁ Δm = list!

  -- ==========================================================================
  -- Region lemmas.  plugˡ: the ambient slot x sits in the Γm-prefix of a
  -- one-slot plug sub (split-here Γm y Δm) N h; substituting g for x
  -- commutes with plugging any h (an instance of sub-interchange, with the
  -- canonical splits reconciled).  Used at h = ⋆/⦅var,var⦆ (to expose the
  -- η-redex after sub) and at h = M (to relate the reduct to the RHS).
  -- ==========================================================================

  plugˡ : ∀ {x y C : Ty} {Θ Γm Ξ₁ Γ Δh Δm : Ctx}
          (s₁ : Split x Θ Γm Ξ₁) (N : Tm (Γm ++ y ∷ Δm) C)
          (g : Tm Γ x) (h : Tm Δh y)
        → PathP (λ i → Tm (flattenˡ Θ Γ Ξ₁ (Δh ++ Δm) i) C)
            (sub (split-here (Θ ++ Γ ++ Ξ₁) y Δm)
              (cast (sym (flattenˡ Θ Γ Ξ₁ (y ∷ Δm)))
                (sub (split-++ˡ s₁ (y ∷ Δm)) N g)) h)
            (sub (split-++ˡ s₁ (Δh ++ Δm)) (sub (split-here Γm y Δm) N h) g)
  plugˡ {x = x} {y = y} {C = C} {Θ = Θ} {Γm = Γm} {Ξ₁ = Ξ₁} {Γ = Γ}
        {Δh = Δh} {Δm = Δm} s₁ N g h =
    tm-over (int-flatˡ Θ Γ Ξ₁ Δh Δm)
      (E₁ ◁ (sub-interchange (split-++ˡ s₁ (y ∷ Δm)) (split-here Ξ₁ y Δm) N g h ▷ E₂))
    where
    Sq : PathP (λ i → Split y (Θ ++ Γ ++ Ξ₁) (flattenˡ Θ Γ Ξ₁ (y ∷ Δm) i) Δm)
               (split-here (Θ ++ Γ ++ Ξ₁) y Δm)
               (split-++ʳ Θ (split-++ʳ Γ (split-here Ξ₁ y Δm)))
    Sq = split-over refl refl (flattenˡ-∙ Θ Γ Ξ₁ (y ∷ Δm))
           (_∙P_ {B = λ Ρ' → Split y (Θ ++ Γ ++ Ξ₁) Ρ' Δm}
                 {p = ++-assoc Θ (Γ ++ Ξ₁) (y ∷ Δm)}
                 {q = ap (Θ ++_) (++-assoc Γ Ξ₁ (y ∷ Δm))}
             (symP (split-here-++ʳ Θ (Γ ++ Ξ₁) y Δm))
             (λ i → split-++ʳ Θ (symP (split-here-++ʳ Γ Ξ₁ y Δm) i)))

    E₁ : sub (split-here (Θ ++ Γ ++ Ξ₁) y Δm)
           (cast (sym (flattenˡ Θ Γ Ξ₁ (y ∷ Δm))) (sub (split-++ˡ s₁ (y ∷ Δm)) N g)) h
       ≡ sub (split-++ʳ Θ (split-++ʳ Γ (split-here Ξ₁ y Δm)))
           (sub (split-++ˡ s₁ (y ∷ Δm)) N g) h
    E₁ = sub-pathp {g = h} {g' = h} Sq
           (symP (cast-filler (sym (flattenˡ Θ Γ Ξ₁ (y ∷ Δm)))
             (sub (split-++ˡ s₁ (y ∷ Δm)) N g)))
           refl

    E₂ : sub (split-++ˡ (split-here Θ x Ξ₁) (Δh ++ Δm))
           (sub (split-behind (split-++ˡ s₁ (y ∷ Δm)) (split-here Ξ₁ y Δm)) N h) g
       ≡ sub (split-++ˡ s₁ (Δh ++ Δm)) (sub (split-here Γm y Δm) N h) g
    E₂ = sub-pathp {W = refl} {g = g} {g' = g}
           (λ i → split-++ˡ (split-canon s₁ i) (Δh ++ Δm))
           (sub-pathp {t = N} {t' = N} {g = h} {g' = h} (behind-here s₁ Δm) refl refl)
           refl

  -- plugʳ: the ambient slot x sits in the Δm-suffix, i.e. BEHIND the plug
  -- slot — sub-interchange read left-to-right with (g into y) and (h into x)
  -- swapped, its right endpoint massaged into split-here form.
  plugʳ : ∀ {x y C : Ty} {Γm Δm Θ₃ Ξ' Γ Δh : Ctx}
          (s₂ : Split x Θ₃ Δm Ξ') (N : Tm (Γm ++ y ∷ Δm) C)
          (g : Tm Γ x) (h : Tm Δh y)
        → PathP (λ i → Tm (interchangeₘ-boundary Γm Δh Θ₃ Γ Ξ' i) C)
            (sub (split-++ʳ Γm (split-++ʳ Δh s₂)) (sub (split-here Γm y Δm) N h) g)
            (sub (split-here Γm y (Θ₃ ++ Γ ++ Ξ'))
              (cast (++-assoc Γm (y ∷ Θ₃) (Γ ++ Ξ'))
                (sub (split-behind (split-here Γm y Δm) s₂) N g)) h)
  plugʳ {x = x} {y = y} {C = C} {Γm = Γm} {Δm = Δm} {Θ₃ = Θ₃} {Ξ' = Ξ'}
        {Γ = Γ} {Δh = Δh} s₂ N g h =
    sub-interchange (split-here Γm y Δm) s₂ N h g ▷ E₂
    where
    E₂ : sub (split-++ˡ (split-here Γm y Θ₃) (Γ ++ Ξ'))
           (sub (split-behind (split-here Γm y Δm) s₂) N g) h
       ≡ sub (split-here Γm y (Θ₃ ++ Γ ++ Ξ'))
           (cast (++-assoc Γm (y ∷ Θ₃) (Γ ++ Ξ'))
             (sub (split-behind (split-here Γm y Δm) s₂) N g)) h
    E₂ = sub-pathp {W = refl} {g = h} {g' = h}
           (split-here-++ˡ Γm y Θ₃ (Γ ++ Ξ'))
           (cast-filler (++-assoc Γm (y ∷ Θ₃) (Γ ++ Ξ'))
             (sub (split-behind (split-here Γm y Δm) s₂) N g))
           refl

  -- midP: the ambient slot x sits in M's region (the middle).  The reduct
  -- sub (split-here Γm y Δm) N (sub s₁' M g) is related to the RHS
  -- sub s (sub (split-here Γm y Δm) N M) g by sub-assoc, with the two view
  -- soundness squares absorbed by sub-pathp and the base reconciled via
  -- flatᵐ-sym / diag-∙.
  midP : ∀ {x y C : Ty} {Θ₂ Ψm Ξ₁' Δm Γm Θ Ξ Γ : Ctx}
         (s₁' : Split x Θ₂ Ψm Ξ₁') (p' : Ξ₁' ++ Δm ≡ Ξ) (q : Γm ++ Θ₂ ≡ Θ)
         {s' : Split x Θ₂ (Ψm ++ Δm) Ξ}
         (co' : PathP (λ i → Split x Θ₂ (Ψm ++ Δm) (p' i)) (split-++ˡ s₁' Δm) s')
         {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
         (co : PathP (λ k → Split x (q k) (Γm ++ Ψm ++ Δm) Ξ) (split-++ʳ Γm s') s)
         (N : Tm (Γm ++ y ∷ Δm) C) (M : Tm Ψm y) (g : Tm Γ x)
       → PathP (λ i → Tm ((flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ k → q k ++ Γ ++ p' k)) i) C)
           (sub (split-here Γm y Δm) N (sub s₁' M g))
           (sub s (sub (split-here Γm y Δm) N M) g)
  midP {x = x} {y = y} {C = C} {Θ₂ = Θ₂} {Ψm = Ψm} {Ξ₁' = Ξ₁'} {Δm = Δm}
       {Γm = Γm} {Ξ = Ξ} {Γ = Γ} s₁' p' q co' co N M g =
    tm-over
      (ap₂ _∙_ (flatᵐ-sym Γm Θ₂ Γ Ξ₁' Δm)
               (sym (diag-∙ (λ Θ' Ξ'' → Θ' ++ Γ ++ Ξ'') q p')))
      (_∙P_ {B = λ Ρ' → Tm Ρ' C}
            {p = sym (assocₘ-boundary Γm Θ₂ Γ Ξ₁' Δm)}
            {q = (λ i → (Γm ++ Θ₂) ++ Γ ++ p' i) ∙ (λ i → q i ++ Γ ++ Ξ)}
        (symP (sub-assoc (split-here Γm y Δm) s₁' N M g))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C}
              {p = λ i → (Γm ++ Θ₂) ++ Γ ++ p' i}
              {q = λ i → q i ++ Γ ++ Ξ}
          (sub-pathp {W = refl}
             {t = sub (split-here Γm y Δm) N M} {t' = sub (split-here Γm y Δm) N M}
             {g = g} {g' = g}
             (λ i → split-++ʳ Γm (co' i)) refl refl)
          (sub-pathp {W = refl}
             {t = sub (split-here Γm y Δm) N M} {t' = sub (split-here Γm y Δm) N M}
             {g = g} {g' = g}
             co refl refl)))

  -- rightP: the ambient slot x sits in the Δm-suffix.  symP plugʳ relates
  -- the reduct (with the doubly-substituted N†) back to the canonically
  -- weakened sub, and the two soundness squares finish, over the bury-based
  -- boundary of sub-match⊗ʳ/sub-match𝟙ʳ's on-right clause.
  rightP : ∀ {x y C : Ty} {Θ₃ Δm Ξ Ψm Θ₂ Γm Θ Γ : Ctx}
           (s₂' : Split x Θ₃ Δm Ξ) (q₂ : Ψm ++ Θ₃ ≡ Θ₂) (q : Γm ++ Θ₂ ≡ Θ)
           {s' : Split x Θ₂ (Ψm ++ Δm) Ξ}
           (co₂ : PathP (λ i → Split x (q₂ i) (Ψm ++ Δm) Ξ) (split-++ʳ Ψm s₂') s')
           {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
           (co : PathP (λ k → Split x (q k) (Γm ++ Ψm ++ Δm) Ξ) (split-++ʳ Γm s') s)
           (N : Tm (Γm ++ y ∷ Δm) C) (M : Tm Ψm y) (g : Tm Γ x)
         → PathP (λ i → Tm ((bury Γm Ψm Θ₃ (Γ ++ Ξ)
                             ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q)) i) C)
             (sub (split-here Γm y (Θ₃ ++ Γ ++ Ξ))
               (cast (++-assoc Γm (y ∷ Θ₃) (Γ ++ Ξ))
                 (sub (split-behind (split-here Γm y Δm) s₂') N g)) M)
             (sub s (sub (split-here Γm y Δm) N M) g)
  rightP {x = x} {y = y} {C = C} {Θ₃ = Θ₃} {Δm = Δm} {Ξ = Ξ} {Ψm = Ψm}
         {Θ₂ = Θ₂} {Γm = Γm} {Γ = Γ} s₂' q₂ q co₂ co N M g =
    tm-over
      (ap₂ _∙_ (int-bury Γm Ψm Θ₃ Γ Ξ)
               (sym (ap-∙ (_++ Γ ++ Ξ) (ap (Γm ++_) q₂) q)))
      (_∙P_ {B = λ Ρ' → Tm Ρ' C}
            {p = sym (interchangeₘ-boundary Γm Ψm Θ₃ Γ Ξ)}
            {q = (λ i → (Γm ++ q₂ i) ++ Γ ++ Ξ) ∙ (λ i → q i ++ Γ ++ Ξ)}
        (symP (plugʳ s₂' N g M))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C}
              {p = λ i → (Γm ++ q₂ i) ++ Γ ++ Ξ}
              {q = λ i → q i ++ Γ ++ Ξ}
          (sub-pathp {W = refl}
             {t = sub (split-here Γm y Δm) N M} {t' = sub (split-here Γm y Δm) N M}
             {g = g} {g' = g}
             (λ i → split-++ʳ Γm (co₂ i)) refl refl)
          (sub-pathp {W = refl}
             {t = sub (split-here Γm y Δm) N M} {t' = sub (split-here Γm y Δm) N M}
             {g = g} {g' = g}
             co refl refl)))

  -- ==========================================================================
  -- η𝟙: match𝟙(M, N[⋆/u])[g/x] ≈ N[M/u][g/x], by regions.
  -- ==========================================================================

  η𝟙-handlerʳ : ∀ {x C : Ty} {Θ₂ Ψm Δm Ξ Γm Θ Γ : Ctx}
      {s' : Split x Θ₂ (Ψm ++ Δm) Ξ}
      (v : Split-++ Ψm Δm s') (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ Ψm ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Ψm 𝟙) (N : Tm (Γm ++ 𝟙 ∷ Δm) C) (g : Tm Γ x)
    → sub-match𝟙ʳ v q M (sub (split-here Γm 𝟙 Δm) N ⋆) g
    ≈ sub s (sub (split-here Γm 𝟙 Δm) N M) g
  η𝟙-handlerʳ {x = x} {C = C} {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁' p' co') q {s = s} co M N g =
    ≈-trans
      (cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ (λ i → q i ++ Γ ++ p' i))
        (η𝟙 {Γm = Γm} {Δm = Δm} (sub s₁' M g) N))
      (pathp→≈ (midP s₁' p' q co' co N M g))
  η𝟙-handlerʳ {x = x} {C = C} {Ψm = Ψm} {Δm = Δm} {Ξ = Ξ} {Γm = Γm} {Γ = Γ}
    (on-right {Θ₂ = Θ₃} s₂' q₂ co₂) q {s = s} co M N g =
    ≈-trans
      (cast-≈ (bury Γm Ψm Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
        (≈-trans
          (match𝟙-cong {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} ≈-refl
            (≈-of-path (from-pathp
              (tm-over (int-flatʳ Γm Θ₃ Γ Ξ) (plugʳ s₂' N g ⋆)))))
          (η𝟙 {Γm = Γm} {Δm = Θ₃ ++ Γ ++ Ξ} M
            (cast (++-assoc Γm (𝟙 ∷ Θ₃) (Γ ++ Ξ))
              (sub (split-behind (split-here Γm 𝟙 Δm) s₂') N g)))))
      (pathp→≈ (rightP s₂' q₂ q co₂ co N M g))

  η𝟙-handler : ∀ {x C : Ty} {Θ Γm Ψm Δm Ξ Γ : Ctx}
      {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
      (v : Split-++ Γm (Ψm ++ Δm) s)
      (M : Tm Ψm 𝟙) (N : Tm (Γm ++ 𝟙 ∷ Δm) C) (g : Tm Γ x)
    → sub-match𝟙ˡ v M (sub (split-here Γm 𝟙 Δm) N ⋆) g
    ≈ sub s (sub (split-here Γm 𝟙 Δm) N M) g
  η𝟙-handler {x = x} {C = C} {Θ = Θ} {Γm = Γm} {Ψm = Ψm} {Δm = Δm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p co) M N g =
    ≈-trans
      (cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψm ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
        (≈-trans
          (match𝟙-cong {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} ≈-refl
            (≈-of-path (from-pathp (symP (plugˡ s₁ N g ⋆)))))
          (η𝟙 {Γm = Θ ++ Γ ++ Ξ₁} {Δm = Δm} M
            (cast (sym (flattenˡ Θ Γ Ξ₁ (𝟙 ∷ Δm)))
              (sub (split-++ˡ s₁ (𝟙 ∷ Δm)) N g)))))
      (pathp→≈
        (_∙P_ {B = λ Ρ' → Tm Ρ' C}
              {p = flattenˡ Θ Γ Ξ₁ (Ψm ++ Δm)} {q = ap (λ Ξ' → Θ ++ Γ ++ Ξ') p}
          (plugˡ s₁ N g M)
          (sub-pathp {W = refl}
             {t = sub (split-here Γm 𝟙 Δm) N M} {t' = sub (split-here Γm 𝟙 Δm) N M}
             {g = g} {g' = g} co refl refl)))
  η𝟙-handler {Ψm = Ψm} (on-right s' q co) M N g =
    η𝟙-handlerʳ (split-++ Ψm s') q co M N g

η𝟙-sub : ∀ {x C : Ty} {Θ Ξ Γ Γm Ψm Δm : Ctx} (s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ)
         (M : Tm Ψm 𝟙) (N : Tm (Γm ++ 𝟙 ∷ Δm) C) (g : Tm Γ x)
       → sub s (match𝟙 {Γ = Γm} {Δ = Δm} M (sub (split-here Γm 𝟙 Δm) N ⋆)) g
       ≈ sub s (sub (split-here Γm 𝟙 Δm) N M) g
η𝟙-sub {Γm = Γm} s M N g = η𝟙-handler (split-++ Γm s) M N g

-- ==========================================================================
-- η⊗: match⊗(M, xy.N[⦅x,y⦆/u])[g/x] ≈ N[M/u][g/x] — same region analysis
-- as η𝟙 with y = A ⊗ B and plug ⦅var,var⦆ (Δh = A ∷ B ∷ []).
-- ==========================================================================

private
  η⊗-handlerʳ : ∀ {x A B C : Ty} {Θ₂ Ψm Δm Ξ Γm Θ Γ : Ctx}
      {s' : Split x Θ₂ (Ψm ++ Δm) Ξ}
      (v : Split-++ Ψm Δm s') (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ Ψm ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Ψm (A ⊗ B)) (N : Tm (Γm ++ (A ⊗ B) ∷ Δm) C) (g : Tm Γ x)
    → sub-match⊗ʳ v q M (sub (split-here Γm (A ⊗ B) Δm) N ⦅ var , var ⦆) g
    ≈ sub s (sub (split-here Γm (A ⊗ B) Δm) N M) g
  η⊗-handlerʳ {x = x} {A = A} {B = B} {C = C} {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁' p' co') q {s = s} co M N g =
    ≈-trans
      (cast-≈ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ (λ i → q i ++ Γ ++ p' i))
        (η⊗ {Γm = Γm} {Δm = Δm} (sub s₁' M g) N))
      (pathp→≈ (midP s₁' p' q co' co N M g))
  η⊗-handlerʳ {x = x} {A = A} {B = B} {C = C} {Ψm = Ψm} {Δm = Δm} {Ξ = Ξ}
    {Γm = Γm} {Γ = Γ}
    (on-right {Θ₂ = Θ₃} s₂' q₂ co₂) q {s = s} co M N g =
    ≈-trans
      (cast-≈ (bury Γm Ψm Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
        (≈-trans
          (match⊗-cong {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} ≈-refl
            (≈-of-path (from-pathp
              (tm-over (int-flatʳ₂ Γm Θ₃ Γ Ξ) (plugʳ s₂' N g ⦅ var , var ⦆)))))
          (η⊗ {Γm = Γm} {Δm = Θ₃ ++ Γ ++ Ξ} M
            (cast (++-assoc Γm ((A ⊗ B) ∷ Θ₃) (Γ ++ Ξ))
              (sub (split-behind (split-here Γm (A ⊗ B) Δm) s₂') N g)))))
      (pathp→≈ (rightP s₂' q₂ q co₂ co N M g))

  η⊗-handler : ∀ {x A B C : Ty} {Θ Γm Ψm Δm Ξ Γ : Ctx}
      {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
      (v : Split-++ Γm (Ψm ++ Δm) s)
      (M : Tm Ψm (A ⊗ B)) (N : Tm (Γm ++ (A ⊗ B) ∷ Δm) C) (g : Tm Γ x)
    → sub-match⊗ˡ v M (sub (split-here Γm (A ⊗ B) Δm) N ⦅ var , var ⦆) g
    ≈ sub s (sub (split-here Γm (A ⊗ B) Δm) N M) g
  η⊗-handler {x = x} {A = A} {B = B} {C = C} {Θ = Θ} {Γm = Γm} {Ψm = Ψm}
    {Δm = Δm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p co) M N g =
    ≈-trans
      (cast-≈ (flattenˡ Θ Γ Ξ₁ (Ψm ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
        (≈-trans
          (match⊗-cong {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} ≈-refl
            (≈-of-path (from-pathp (symP (plugˡ s₁ N g ⦅ var , var ⦆)))))
          (η⊗ {Γm = Θ ++ Γ ++ Ξ₁} {Δm = Δm} M
            (cast (sym (flattenˡ Θ Γ Ξ₁ ((A ⊗ B) ∷ Δm)))
              (sub (split-++ˡ s₁ ((A ⊗ B) ∷ Δm)) N g)))))
      (pathp→≈
        (_∙P_ {B = λ Ρ' → Tm Ρ' C}
              {p = flattenˡ Θ Γ Ξ₁ (Ψm ++ Δm)} {q = ap (λ Ξ' → Θ ++ Γ ++ Ξ') p}
          (plugˡ s₁ N g M)
          (sub-pathp {W = refl}
             {t = sub (split-here Γm (A ⊗ B) Δm) N M}
             {t' = sub (split-here Γm (A ⊗ B) Δm) N M}
             {g = g} {g' = g} co refl refl)))
  η⊗-handler {Ψm = Ψm} (on-right s' q co) M N g =
    η⊗-handlerʳ (split-++ Ψm s') q co M N g

η⊗-sub : ∀ {x A B C : Ty} {Θ Ξ Γ Γm Ψm Δm : Ctx}
         (s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ)
         (M : Tm Ψm (A ⊗ B)) (N : Tm (Γm ++ (A ⊗ B) ∷ Δm) C) (g : Tm Γ x)
       → sub s (match⊗ {Γ = Γm} {Δ = Δm} M
           (sub (split-here Γm (A ⊗ B) Δm) N ⦅ var , var ⦆)) g
       ≈ sub s (sub (split-here Γm (A ⊗ B) Δm) N M) g
η⊗-sub {Γm = Γm} s M N g = η⊗-handler (split-++ Γm s) M N g

-- ==========================================================================
-- β⊗ machinery.  Each region case fires β⊗ at the substituted configuration
-- and reconciles the reduct with sub s R g (R the rule's cast reduct) via
-- sub-assoc / sub-interchange, a structural split-line over β⊗-boundary,
-- and a core base-path coherence proved cons-by-cons.
-- ==========================================================================

private
  -- One-dimensional shuffles.
  sh₃ : ∀ {ℓ} {X : Type ℓ} {a b c d e : X}
        (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (T : d ≡ e)
      → p ∙ (q ∙ (r ∙ T)) ≡ (p ∙ (q ∙ r)) ∙ T
  sh₃ p q r T = ap (p ∙_) (∙-assoc q r T) ∙ ∙-assoc p (q ∙ r) T

  -- Cons step for base-path coherences: distribute ap f over a
  -- three-segment ≡ two-segment equation.
  ap-eq₃₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e : X}
            {p₁ : a ≡ b} {p₂ : b ≡ c} {p₃ : c ≡ d} {q₁ : a ≡ e} {q₂ : e ≡ d}
          → p₁ ∙ (p₂ ∙ p₃) ≡ q₁ ∙ q₂
          → ap f p₁ ∙ (ap f p₂ ∙ ap f p₃) ≡ ap f q₁ ∙ ap f q₂
  ap-eq₃₂ f {p₁ = p₁} {p₂ = p₂} {p₃ = p₃} {q₁ = q₁} {q₂ = q₂} eq =
    ap (ap f p₁ ∙_) (sym (ap-∙ f p₂ p₃))
    ∙ sym (ap-∙ f p₁ (p₂ ∙ p₃))
    ∙ ap (ap f) eq
    ∙ ap-∙ f q₁ q₂

  -- The slot sits in Δ₁ (the pair's right component): the canonical x-split
  -- of X₂'s context, transported across β⊗-boundary.
  split-ββᴮ : ∀ (Γm : Ctx) {x : Ty} {Θ₂₂ Δ₁ Ξ₁' : Ctx}
              (s₂ : Split x Θ₂₂ Δ₁ Ξ₁') (Γ₁ Δm : Ctx)
            → PathP (λ i → Split x (++-assoc Γm Γ₁ Θ₂₂ i)
                                   (β⊗-boundary Γm Γ₁ Δ₁ Δm i)
                                   (Ξ₁' ++ Δm))
                (split-++ʳ (Γm ++ Γ₁) (split-++ˡ s₂ Δm))
                (split-++ʳ Γm (split-++ˡ (split-++ʳ Γ₁ s₂) Δm))
  split-ββᴮ []       s₂ Γ₁ Δm = symP (split-++ˡʳ-comm Γ₁ s₂ Δm)
  split-ββᴮ (a ∷ Γm) s₂ Γ₁ Δm i = there (split-ββᴮ Γm s₂ Γ₁ Δm i)

  -- Core coherence for the Δ₁-region: the composite of the fired boundary,
  -- the associativity boundary and the prefix reassociation is the clause's
  -- pair-cast followed by flattenᵐ at the pre-view suffix.
  core2bΓ : ∀ (Γ₁ Θ₂₂ Γ Ξ₁' Δm : Ctx)
          → ++-assoc Γ₁ (Θ₂₂ ++ Γ ++ Ξ₁') Δm
            ∙ (sym (assocₘ-boundary Γ₁ Θ₂₂ Γ Ξ₁' Δm)
               ∙ (λ _ → (Γ₁ ++ Θ₂₂) ++ Γ ++ (Ξ₁' ++ Δm)))
          ≡ (λ i → flattenʳ Γ₁ Θ₂₂ Γ Ξ₁' i ++ Δm)
            ∙ flattenˡ (Γ₁ ++ Θ₂₂) Γ Ξ₁' Δm
  core2bΓ Γ₁ Θ₂₂ Γ Ξ₁' Δm = list!

  core2b : ∀ (Γm Γ₁ Θ₂₂ Γ Ξ₁' Δm : Ctx)
         → sym (β⊗-boundary Γm Γ₁ (Θ₂₂ ++ Γ ++ Ξ₁') Δm)
           ∙ (sym (assocₘ-boundary (Γm ++ Γ₁) Θ₂₂ Γ Ξ₁' Δm)
              ∙ (λ i → ++-assoc Γm Γ₁ Θ₂₂ i ++ Γ ++ (Ξ₁' ++ Δm)))
         ≡ (λ i → Γm ++ flattenʳ Γ₁ Θ₂₂ Γ Ξ₁' i ++ Δm)
           ∙ flattenᵐ Γm (Γ₁ ++ Θ₂₂) Γ Ξ₁' Δm
  core2b Γm Γ₁ Θ₂₂ Γ Ξ₁' Δm = list!

  -- Case: the ambient slot x sits in Δ₁ (the pair's right component).
  -- One sub-assoc (g goes through N into the B-slot plug), then the
  -- boundary split-line and the three view soundness squares.
  β⊗-pairR-case :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Θ₂ Ξ₁' Θ₂₂ : Ctx}
      (s₂'' : Split x Θ₂₂ Δ₁ Ξ₁') (q'' : Γ₁ ++ Θ₂₂ ≡ Θ₂)
      {s₁' : Split x Θ₂ (Γ₁ ++ Δ₁) Ξ₁'}
      (co'' : PathP (λ i → Split x (q'' i) (Γ₁ ++ Δ₁) Ξ₁') (split-++ʳ Γ₁ s₂'') s₁')
      (p' : Ξ₁' ++ Δm ≡ Ξ)
      {s' : Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co' : PathP (λ i → Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) (p' i)) (split-++ˡ s₁' Δm) s')
      (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → cast (flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ i → q i ++ Γ ++ p' i))
        (match⊗ {Γ = Γm} {Δ = Δm}
          (cast (flattenʳ Γ₁ Θ₂₂ Γ Ξ₁' ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ₁') q'')
            ⦅ M , sub s₂'' N g ⦆)
          P)
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-pairR-case {x = x} {A = A} {B = B} {C = C} {Θ = Θ} {Ξ = Ξ} {Γ = Γ}
    {Γm = Γm} {Δm = Δm} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Θ₂ = Θ₂} {Ξ₁' = Ξ₁'} {Θ₂₂ = Θ₂₂}
    s₂'' q'' {s₁' = s₁'} co'' p' {s' = s'} co' q {s = s} co M N P g =
    ≈-trans (≈←pathp KL)
      (≈-trans (cast-≈ DL (β⊗ {Γm = Γm} {Δm = Δm} M (sub s₂'' N g) P))
        (pathp→≈ (tm-over αᵇ Kchain)))
    where
    ηc   = λ (w : Ctx) → Γm ++ w ++ Δm
    c₂ᵇ  = flattenʳ Γ₁ Θ₂₂ Γ Ξ₁' ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ₁') q''
    BIG₂ = flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ i → q i ++ Γ ++ p' i)
    DL   = (λ i → Γm ++ c₂ᵇ i ++ Δm) ∙ BIG₂
    pair* = ⦅ M , sub s₂'' N g ⦆
    W    = match⊗ {Γ = Γm} {Δ = Δm} pair* P
    X₁   = sub (split-here Γm A (B ∷ Δm)) P M
    X₂   = sub (split-++ʳ Γm (split-here Γ₁ B Δm)) X₁ N
    R    = cast (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂
    bb*  = β⊗-boundary Γm Γ₁ (Θ₂₂ ++ Γ ++ Ξ₁') Δm
    Y*   = sub (split-++ʳ Γm (split-here Γ₁ B Δm)) X₁ (sub s₂'' N g)
    AB₂  = assocₘ-boundary (Γm ++ Γ₁) Θ₂₂ Γ Ξ₁' Δm
    B3   = λ i → ++-assoc Γm Γ₁ Θ₂₂ i ++ Γ ++ (Ξ₁' ++ Δm)
    B4   = λ i → (Γm ++ q'' i) ++ Γ ++ (Ξ₁' ++ Δm)
    B5   = λ i → (Γm ++ Θ₂) ++ Γ ++ p' i
    B6   = λ i → q i ++ Γ ++ Ξ
    fθ   = λ (Θ' : Ctx) → Γm ++ (Θ' ++ Γ ++ Ξ₁') ++ Δm
    gθ   = λ (Θ' : Ctx) → (Γm ++ Θ') ++ Γ ++ (Ξ₁' ++ Δm)
    Hθ   = λ (Θ' : Ctx) → flattenᵐ Γm Θ' Γ Ξ₁' Δm
    apηF = λ i → Γm ++ flattenʳ Γ₁ Θ₂₂ Γ Ξ₁' i ++ Δm
    Hmid = flattenᵐ Γm (Γ₁ ++ Θ₂₂) Γ Ξ₁' Δm
    HΘ₂  = flattenᵐ Γm Θ₂ Γ Ξ₁' Δm

    KL : PathP (λ i → Tm (DL i) C) W
           (cast BIG₂ (match⊗ {Γ = Γm} {Δ = Δm} (cast c₂ᵇ pair*) P))
    KL = _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = λ i → Γm ++ c₂ᵇ i ++ Δm} {q = BIG₂}
           (λ i → match⊗ {Γ = Γm} {Δ = Δm} (cast-filler c₂ᵇ pair* i) P)
           (cast-filler BIG₂ (match⊗ {Γ = Γm} {Δ = Δm} (cast c₂ᵇ pair*) P))

    Kchain : PathP (λ i → Tm ((sym bb* ∙ (sym AB₂ ∙ (B3 ∙ (B4 ∙ (B5 ∙ B6))))) i) C)
               (cast bb* Y*) (sub s R g)
    Kchain =
      _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym bb*} {q = sym AB₂ ∙ (B3 ∙ (B4 ∙ (B5 ∙ B6)))}
        (symP (cast-filler bb* Y*))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym AB₂} {q = B3 ∙ (B4 ∙ (B5 ∙ B6))}
          (symP (sub-assoc (split-++ʳ Γm (split-here Γ₁ B Δm)) s₂'' X₁ N g))
          (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B3} {q = B4 ∙ (B5 ∙ B6)}
            (sub-pathp {W = refl} {g = g} {g' = g}
              (split-ββᴮ Γm s₂'' Γ₁ Δm)
              (cast-filler (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂) refl)
            (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B4} {q = B5 ∙ B6}
              (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                (λ i → split-++ʳ Γm (split-++ˡ (co'' i) Δm)) refl refl)
              (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B5} {q = B6}
                (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                  (λ i → split-++ʳ Γm (co' i)) refl refl)
                (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                  co refl refl)))))

    αᵇ : sym bb* ∙ (sym AB₂ ∙ (B3 ∙ (B4 ∙ (B5 ∙ B6)))) ≡ DL
    αᵇ =
      sh₃ (sym bb*) (sym AB₂) B3 (B4 ∙ (B5 ∙ B6))
      ∙ ap (_∙ (B4 ∙ (B5 ∙ B6))) (core2b Γm Γ₁ Θ₂₂ Γ Ξ₁' Δm)
      ∙ sym (∙-assoc apηF Hmid (B4 ∙ (B5 ∙ B6)))
      ∙ ap (apηF ∙_) (∙-assoc Hmid B4 (B5 ∙ B6))
      ∙ ap (λ w → apηF ∙ (w ∙ (B5 ∙ B6)))
           (homotopy-natural {f = fθ} {g = gθ} Hθ q'')
      ∙ ap (apηF ∙_) (sym (∙-assoc (ap fθ q'') HΘ₂ (B5 ∙ B6)))
      ∙ ∙-assoc apηF (ap fθ q'') (HΘ₂ ∙ (B5 ∙ B6))
      ∙ ap (_∙ (HΘ₂ ∙ (B5 ∙ B6)))
           (sym (ap-∙ ηc (flattenʳ Γ₁ Θ₂₂ Γ Ξ₁') (ap (λ Θ' → Θ' ++ Γ ++ Ξ₁') q'')))
      ∙ ap (λ w → ap ηc c₂ᵇ ∙ (HΘ₂ ∙ w))
           (sym (diag-∙ (λ Θ' Ξ'' → Θ' ++ Γ ++ Ξ'') q p'))

  sh₄ : ∀ {ℓ} {X : Type ℓ} {a b c d e f : X}
        (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (u : d ≡ e) (T : e ≡ f)
      → p ∙ (q ∙ (r ∙ (u ∙ T))) ≡ (p ∙ (q ∙ (r ∙ u))) ∙ T
  sh₄ p q r u T =
    ap (p ∙_) (ap (q ∙_) (∙-assoc r u T))
    ∙ ap (p ∙_) (∙-assoc q (r ∙ u) T)
    ∙ ∙-assoc p (q ∙ (r ∙ u)) T

  ap-eq₄₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e w : X}
            {p₁ : a ≡ b} {p₂ : b ≡ c} {p₃ : c ≡ d} {p₄ : d ≡ e}
            {q₁ : a ≡ w} {q₂ : w ≡ e}
          → p₁ ∙ (p₂ ∙ (p₃ ∙ p₄)) ≡ q₁ ∙ q₂
          → ap f p₁ ∙ (ap f p₂ ∙ (ap f p₃ ∙ ap f p₄)) ≡ ap f q₁ ∙ ap f q₂
  ap-eq₄₂ f {p₁ = p₁} {p₂ = p₂} {p₃ = p₃} {p₄ = p₄} {q₁ = q₁} {q₂ = q₂} eq =
    ap (ap f p₁ ∙_) (ap (ap f p₂ ∙_) (sym (ap-∙ f p₃ p₄)))
    ∙ ap (ap f p₁ ∙_) (sym (ap-∙ f p₂ (p₃ ∙ p₄)))
    ∙ sym (ap-∙ f p₁ (p₂ ∙ (p₃ ∙ p₄)))
    ∙ ap (ap f) eq
    ∙ ap-∙ f q₁ q₂

  -- The ++-assoc pentagon (with a unit segment kept where the flattenʳ of
  -- the enclosing induction degenerates).
  pentagon : ∀ (Γ Ξ Δ₁ Δm : Ctx)
           → ++-assoc (Γ ++ Ξ) Δ₁ Δm
             ∙ ((λ _ → (Γ ++ Ξ) ++ Δ₁ ++ Δm)
                ∙ (++-assoc Γ Ξ (Δ₁ ++ Δm)
                   ∙ ap (Γ ++_) (sym (++-assoc Ξ Δ₁ Δm))))
           ≡ ap (_++ Δm) (++-assoc Γ Ξ Δ₁) ∙ ++-assoc Γ (Ξ ++ Δ₁) Δm
  pentagon Γ Ξ Δ₁ Δm = list!

  -- Core coherence for the Γ₁-region, Θ₂-level (Γm = []).
  core2aΘ : ∀ (Θ₂ Γ Ξ₁ Δ₁ Δm : Ctx)
          → ++-assoc (Θ₂ ++ Γ ++ Ξ₁) Δ₁ Δm
            ∙ ((λ i → flattenʳ [] Θ₂ Γ Ξ₁ i ++ Δ₁ ++ Δm)
               ∙ (interchangeₘ-boundary Θ₂ Γ Ξ₁ Δ₁ Δm
                  ∙ (λ i → Θ₂ ++ Γ ++ ++-assoc Ξ₁ Δ₁ Δm (~ i))))
          ≡ (λ i → flattenˡ Θ₂ Γ Ξ₁ Δ₁ i ++ Δm) ∙ flattenˡ Θ₂ Γ (Ξ₁ ++ Δ₁) Δm
  core2aΘ Θ₂ Γ Ξ₁ Δ₁ Δm = list!

  core2a : ∀ (Γm Θ₂ Γ Ξ₁ Δ₁ Δm : Ctx)
         → sym (β⊗-boundary Γm (Θ₂ ++ Γ ++ Ξ₁) Δ₁ Δm)
           ∙ ((λ i → flattenʳ Γm Θ₂ Γ Ξ₁ i ++ Δ₁ ++ Δm)
              ∙ (interchangeₘ-boundary (Γm ++ Θ₂) Γ Ξ₁ Δ₁ Δm
                 ∙ (λ i → (Γm ++ Θ₂) ++ Γ ++ ++-assoc Ξ₁ Δ₁ Δm (~ i))))
         ≡ (λ i → Γm ++ flattenˡ Θ₂ Γ Ξ₁ Δ₁ i ++ Δm)
           ∙ flattenᵐ Γm Θ₂ Γ (Ξ₁ ++ Δ₁) Δm
  core2a Γm Θ₂ Γ Ξ₁ Δ₁ Δm = list!

  -- The canonical B-slot after the middle-region reduction, against the
  -- fully weakened one sub-interchange expects (base case is plugˡ's Sq).
  sq-here-mid : ∀ (Γm Θ₂ Γ Ξ₁ : Ctx) (y : Ty) (Δm : Ctx)
              → PathP (λ i → Split y (flattenʳ Γm Θ₂ Γ Ξ₁ i)
                                     (flattenᵐ Γm Θ₂ Γ Ξ₁ (y ∷ Δm) i) Δm)
                  (split-++ʳ Γm (split-here (Θ₂ ++ Γ ++ Ξ₁) y Δm))
                  (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-here Ξ₁ y Δm)))
  sq-here-mid [] Θ₂ Γ Ξ₁ y Δm =
    split-over refl refl (flattenˡ-∙ Θ₂ Γ Ξ₁ (y ∷ Δm))
      (_∙P_ {B = λ Ρ' → Split y (Θ₂ ++ Γ ++ Ξ₁) Ρ' Δm}
            {p = ++-assoc Θ₂ (Γ ++ Ξ₁) (y ∷ Δm)}
            {q = ap (Θ₂ ++_) (++-assoc Γ Ξ₁ (y ∷ Δm))}
        (symP (split-here-++ʳ Θ₂ (Γ ++ Ξ₁) y Δm))
        (λ i → split-++ʳ Θ₂ (symP (split-here-++ʳ Γ Ξ₁ y Δm) i)))
  sq-here-mid (a ∷ Γm) Θ₂ Γ Ξ₁ y Δm i = there (sq-here-mid Γm Θ₂ Γ Ξ₁ y Δm i)

  -- split-behind against the canonical inner split, under a prefix
  -- weakening (base case is behind-here).
  behind-++ʳ-here : ∀ (Γm : Ctx) {x y : Ty} {Θ₂ Γ₁ Ξ₁ : Ctx}
                    (s₁ : Split x Θ₂ Γ₁ Ξ₁) (Δm : Ctx)
                  → PathP (λ i → Split y (split-path (split-++ʳ Γm s₁) i)
                                         (Γm ++ Γ₁ ++ y ∷ Δm) Δm)
                      (split-behind (split-++ʳ Γm (split-++ˡ s₁ (y ∷ Δm)))
                                    (split-here Ξ₁ y Δm))
                      (split-++ʳ Γm (split-here Γ₁ y Δm))
  behind-++ʳ-here []       s₁ Δm = behind-here s₁ Δm
  behind-++ʳ-here (a ∷ Γm) s₁ Δm i = there (behind-++ʳ-here Γm s₁ Δm i)

  -- The slot sits in Γ₁ (the pair's left component): the canonical x-split
  -- of X₂'s context, transported across β⊗-boundary.
  split-ββʳ : ∀ (Γm : Ctx) {x : Ty} {Θ₂ Γ₁ Ξ₁ : Ctx}
              (s₁ : Split x Θ₂ Γ₁ Ξ₁) (Δ₁ Δm : Ctx)
            → PathP (λ i → Split x (Γm ++ Θ₂)
                                   (β⊗-boundary Γm Γ₁ Δ₁ Δm i)
                                   (++-assoc Ξ₁ Δ₁ Δm (~ i)))
                (split-++ˡ (split-++ʳ Γm s₁) (Δ₁ ++ Δm))
                (split-++ʳ Γm (split-++ˡ (split-++ˡ s₁ Δ₁) Δm))
  split-ββʳ []       s₁ Δ₁ Δm = symP (split-++ˡ-++ s₁ Δ₁ Δm)
  split-ββʳ (a ∷ Γm) s₁ Δ₁ Δm i = there (split-ββʳ Γm s₁ Δ₁ Δm i)

  -- Case: the ambient slot x sits in Γ₁ (the pair's left component).
  -- One sub-assoc (g through M into the A-slot plug), one sub-interchange
  -- (g past the B-slot plug), then boundary split-line and soundness squares.
  β⊗-pairL-case :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Θ₂ Ξ₁' Ξ₁'' : Ctx}
      (s₁'' : Split x Θ₂ Γ₁ Ξ₁'') (p'' : Ξ₁'' ++ Δ₁ ≡ Ξ₁')
      {s₁' : Split x Θ₂ (Γ₁ ++ Δ₁) Ξ₁'}
      (co'' : PathP (λ i → Split x Θ₂ (Γ₁ ++ Δ₁) (p'' i)) (split-++ˡ s₁'' Δ₁) s₁')
      (p' : Ξ₁' ++ Δm ≡ Ξ)
      {s' : Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co' : PathP (λ i → Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) (p' i)) (split-++ˡ s₁' Δm) s')
      (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → cast (flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ i → q i ++ Γ ++ p' i))
        (match⊗ {Γ = Γm} {Δ = Δm}
          (cast (flattenˡ Θ₂ Γ Ξ₁'' Δ₁ ∙ ap (λ Ξ' → Θ₂ ++ Γ ++ Ξ') p'')
            ⦅ sub s₁'' M g , N ⦆)
          P)
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-pairL-case {x = x} {A = A} {B = B} {C = C} {Θ = Θ} {Ξ = Ξ} {Γ = Γ}
    {Γm = Γm} {Δm = Δm} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Θ₂ = Θ₂} {Ξ₁' = Ξ₁'} {Ξ₁'' = Ξ₁''}
    s₁'' p'' {s₁' = s₁'} co'' p' {s' = s'} co' q {s = s} co M N P g =
    ≈-trans (≈←pathp KL)
      (≈-trans (cast-≈ DL (β⊗ {Γm = Γm} {Δm = Δm} (sub s₁'' M g) N P))
        (pathp→≈ (tm-over αᵃ Kchain)))
    where
    ηc   = λ (w : Ctx) → Γm ++ w ++ Δm
    c₂ᵃ  = flattenˡ Θ₂ Γ Ξ₁'' Δ₁ ∙ ap (λ Ξ' → Θ₂ ++ Γ ++ Ξ') p''
    BIG₂ = flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ i → q i ++ Γ ++ p' i)
    DL   = (λ i → Γm ++ c₂ᵃ i ++ Δm) ∙ BIG₂
    pair* = ⦅ sub s₁'' M g , N ⦆
    W    = match⊗ {Γ = Γm} {Δ = Δm} pair* P
    SA   = split-here Γm A (B ∷ Δm)
    X₁   = sub SA P M
    X₂   = sub (split-++ʳ Γm (split-here Γ₁ B Δm)) X₁ N
    R    = cast (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂
    bb*  = β⊗-boundary Γm (Θ₂ ++ Γ ++ Ξ₁'') Δ₁ Δm
    Y*   = sub (split-++ʳ Γm (split-here (Θ₂ ++ Γ ++ Ξ₁'') B Δm))
             (sub SA P (sub s₁'' M g)) N
    F₂a  = λ i → flattenʳ Γm Θ₂ Γ Ξ₁'' i ++ Δ₁ ++ Δm
    IB₂a = interchangeₘ-boundary (Γm ++ Θ₂) Γ Ξ₁'' Δ₁ Δm
    B4a  = λ i → (Γm ++ Θ₂) ++ Γ ++ ++-assoc Ξ₁'' Δ₁ Δm (~ i)
    B5a  = λ i → (Γm ++ Θ₂) ++ Γ ++ (p'' i ++ Δm)
    B6a  = λ i → (Γm ++ Θ₂) ++ Γ ++ p' i
    B7a  = λ i → q i ++ Γ ++ Ξ
    fη   = λ (Ξ' : Ctx) → Γm ++ (Θ₂ ++ Γ ++ Ξ') ++ Δm
    gη   = λ (Ξ' : Ctx) → (Γm ++ Θ₂) ++ Γ ++ (Ξ' ++ Δm)
    Hη   = λ (Ξ' : Ctx) → flattenᵐ Γm Θ₂ Γ Ξ' Δm
    apF  = λ i → Γm ++ flattenˡ Θ₂ Γ Ξ₁'' Δ₁ i ++ Δm
    Hmid = flattenᵐ Γm Θ₂ Γ (Ξ₁'' ++ Δ₁) Δm
    HΞ   = flattenᵐ Γm Θ₂ Γ Ξ₁' Δm

    KL : PathP (λ i → Tm (DL i) C) W
           (cast BIG₂ (match⊗ {Γ = Γm} {Δ = Δm} (cast c₂ᵃ pair*) P))
    KL = _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = λ i → Γm ++ c₂ᵃ i ++ Δm} {q = BIG₂}
           (λ i → match⊗ {Γ = Γm} {Δ = Δm} (cast-filler c₂ᵃ pair* i) P)
           (cast-filler BIG₂ (match⊗ {Γ = Γm} {Δ = Δm} (cast c₂ᵃ pair*) P))

    SqMid : PathP (λ i → Split B (flattenʳ Γm Θ₂ Γ Ξ₁'' i)
                                 (sym (assocₘ-boundary Γm Θ₂ Γ Ξ₁'' (B ∷ Δm)) i) Δm)
              (split-++ʳ Γm (split-here (Θ₂ ++ Γ ++ Ξ₁'') B Δm))
              (split-++ʳ (Γm ++ Θ₂) (split-++ʳ Γ (split-here Ξ₁'' B Δm)))
    SqMid = split-over refl refl (sym (flatᵐ-sym Γm Θ₂ Γ Ξ₁'' (B ∷ Δm)))
              (sq-here-mid Γm Θ₂ Γ Ξ₁'' B Δm)

    E₂C : sub (split-++ˡ (split-here (Γm ++ Θ₂) x Ξ₁'') (Δ₁ ++ Δm))
            (sub (split-behind (split-++ʳ Γm (split-++ˡ s₁'' (B ∷ Δm)))
                               (split-here Ξ₁'' B Δm)) X₁ N) g
        ≡ sub (split-++ˡ (split-++ʳ Γm s₁'') (Δ₁ ++ Δm)) X₂ g
    E₂C = sub-pathp {W = refl} {g = g} {g' = g}
            (λ i → split-++ˡ (split-canon (split-++ʳ Γm s₁'') i) (Δ₁ ++ Δm))
            (sub-pathp {W = refl} {t = X₁} {t' = X₁} {g = N} {g' = N}
              (behind-++ʳ-here Γm s₁'' Δm) refl refl)
            refl

    Kchain : PathP (λ i → Tm ((sym bb* ∙ (F₂a ∙ (IB₂a ∙ (B4a ∙ (B5a ∙ (B6a ∙ B7a)))))) i) C)
               (cast bb* Y*) (sub s R g)
    Kchain =
      _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym bb*}
           {q = F₂a ∙ (IB₂a ∙ (B4a ∙ (B5a ∙ (B6a ∙ B7a))))}
        (symP (cast-filler bb* Y*))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = F₂a}
              {q = IB₂a ∙ (B4a ∙ (B5a ∙ (B6a ∙ B7a)))}
          (sub-pathp {W = refl} {g = N} {g' = N} SqMid
            (symP (sub-assoc SA s₁'' P M g)) refl)
          (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = IB₂a}
                {q = B4a ∙ (B5a ∙ (B6a ∙ B7a))}
            (sub-interchange (split-++ʳ Γm (split-++ˡ s₁'' (B ∷ Δm)))
               (split-here Ξ₁'' B Δm) X₁ g N ▷ E₂C)
            (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B4a} {q = B5a ∙ (B6a ∙ B7a)}
              (sub-pathp {W = refl} {g = g} {g' = g}
                (split-ββʳ Γm s₁'' Δ₁ Δm)
                (cast-filler (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂) refl)
              (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B5a} {q = B6a ∙ B7a}
                (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                  (λ i → split-++ʳ Γm (split-++ˡ (co'' i) Δm)) refl refl)
                (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B6a} {q = B7a}
                  (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                    (λ i → split-++ʳ Γm (co' i)) refl refl)
                  (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                    co refl refl))))))

    αᵃ : sym bb* ∙ (F₂a ∙ (IB₂a ∙ (B4a ∙ (B5a ∙ (B6a ∙ B7a))))) ≡ DL
    αᵃ =
      sh₄ (sym bb*) F₂a IB₂a B4a (B5a ∙ (B6a ∙ B7a))
      ∙ ap (_∙ (B5a ∙ (B6a ∙ B7a))) (core2a Γm Θ₂ Γ Ξ₁'' Δ₁ Δm)
      ∙ sym (∙-assoc apF Hmid (B5a ∙ (B6a ∙ B7a)))
      ∙ ap (apF ∙_) (∙-assoc Hmid B5a (B6a ∙ B7a))
      ∙ ap (λ w → apF ∙ (w ∙ (B6a ∙ B7a)))
           (homotopy-natural {f = fη} {g = gη} Hη p'')
      ∙ ap (apF ∙_) (sym (∙-assoc (ap fη p'') HΞ (B6a ∙ B7a)))
      ∙ ∙-assoc apF (ap fη p'') (HΞ ∙ (B6a ∙ B7a))
      ∙ ap (_∙ (HΞ ∙ (B6a ∙ B7a)))
           (sym (ap-∙ ηc (flattenˡ Θ₂ Γ Ξ₁'' Δ₁) (ap (λ Ξ' → Θ₂ ++ Γ ++ Ξ') p'')))
      ∙ ap (λ w → ap ηc c₂ᵃ ∙ (HΞ ∙ w))
           (sym (diag-∙ (λ Θ' Ξ'' → Θ' ++ Γ ++ Ξ'') q p'))

  ap-eq₄₁ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e : X}
            {p₁ : a ≡ b} {p₂ : b ≡ c} {p₃ : c ≡ d} {p₄ : d ≡ e} {q : a ≡ e}
          → p₁ ∙ (p₂ ∙ (p₃ ∙ p₄)) ≡ q
          → ap f p₁ ∙ (ap f p₂ ∙ (ap f p₃ ∙ ap f p₄)) ≡ ap f q
  ap-eq₄₁ f {p₁ = p₁} {p₂ = p₂} {p₃ = p₃} {p₄ = p₄} eq =
    ap (ap f p₁ ∙_) (ap (ap f p₂ ∙_) (sym (ap-∙ f p₃ p₄)))
    ∙ ap (ap f p₁ ∙_) (sym (ap-∙ f p₂ (p₃ ∙ p₄)))
    ∙ sym (ap-∙ f p₁ (p₂ ∙ (p₃ ∙ p₄)))
    ∙ ap (ap f) eq

  -- Prefix weakening through the three-part flatten (base: split-++ʳ-++).
  sq-++ʳ-flatten : ∀ (Θ Γ Ξ₁ : Ctx) {y : Ty} {Θw Λw Ξw : Ctx}
                   (w : Split y Θw Λw Ξw)
                 → PathP (λ i → Split y (flattenˡ Θ Γ Ξ₁ Θw i)
                                        (flattenˡ Θ Γ Ξ₁ Λw i) Ξw)
                     (split-++ʳ (Θ ++ Γ ++ Ξ₁) w)
                     (split-++ʳ Θ (split-++ʳ Γ (split-++ʳ Ξ₁ w)))
  sq-++ʳ-flatten []      Γ Ξ₁ w = split-++ʳ-++ Γ Ξ₁ w
  sq-++ʳ-flatten (a ∷ Θ) Γ Ξ₁ w i = there (sq-++ʳ-flatten Θ Γ Ξ₁ w i)

  -- split-behind against the canonical inner split, under a suffix
  -- weakening (base and steps mirror behind-here).
  behind-hereˡ : ∀ {x y : Ty} {Θ Γm Ξ₁ : Ctx}
                 (s₁ : Split x Θ Γm Ξ₁) (Γ₁ Δm : Ctx)
               → PathP (λ i → Split y (split-path (split-++ˡ s₁ Γ₁) i)
                                      (Γm ++ Γ₁ ++ y ∷ Δm) Δm)
                   (split-behind (split-++ˡ s₁ (Γ₁ ++ y ∷ Δm))
                                 (split-++ʳ Ξ₁ (split-here Γ₁ y Δm)))
                   (split-++ʳ Γm (split-here Γ₁ y Δm))
  behind-hereˡ here       Γ₁ Δm = refl
  behind-hereˡ (there s₁) Γ₁ Δm i = there (behind-hereˡ s₁ Γ₁ Δm i)

  -- The slot sits in Γm: the canonical x-split of X₂'s context, transported
  -- across β⊗-boundary (which also reassociates the suffix).
  split-ββ : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (Γ₁ Δ₁ Δm : Ctx)
           → PathP (λ i → Split x Θ (β⊗-boundary Γm Γ₁ Δ₁ Δm i)
                                    (β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i))
               (split-++ˡ (split-++ˡ s₁ Γ₁) (Δ₁ ++ Δm))
               (split-++ˡ s₁ ((Γ₁ ++ Δ₁) ++ Δm))
  split-ββ (here {Ξ = Ξ₁}) Γ₁ Δ₁ Δm i = here {Ξ = β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i}
  split-ββ (there s₁)      Γ₁ Δ₁ Δm i = there (split-ββ s₁ Γ₁ Δ₁ Δm i)

  -- Core coherence for the Γm-region, Γ-level (Θ = []).
  core1Γ : ∀ (Γ Ξ₁ Γ₁ Δ₁ Δm : Ctx)
         → sym (β⊗-boundary (Γ ++ Ξ₁) Γ₁ Δ₁ Δm)
           ∙ ((λ i → ++-assoc Γ Ξ₁ Γ₁ i ++ Δ₁ ++ Δm)
              ∙ (++-assoc Γ (Ξ₁ ++ Γ₁) (Δ₁ ++ Δm)
                 ∙ (λ i → Γ ++ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i)))
         ≡ ++-assoc Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm)
  core1Γ [] Ξ₁ Γ₁ Δ₁ Δm =
      ap (sym (β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm) ∙_)
         (∙-idl (refl ∙ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm))
    ∙ ap (sym (β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm) ∙_) (∙-idl (β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm))
    ∙ ∙-invl (β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm)
  core1Γ (a ∷ Γ) Ξ₁ Γ₁ Δ₁ Δm =
    ap-eq₄₁ (a ∷_)
      {p₁ = sym (β⊗-boundary (Γ ++ Ξ₁) Γ₁ Δ₁ Δm)}
      {p₂ = λ i → ++-assoc Γ Ξ₁ Γ₁ i ++ Δ₁ ++ Δm}
      {p₃ = ++-assoc Γ (Ξ₁ ++ Γ₁) (Δ₁ ++ Δm)}
      {p₄ = λ i → Γ ++ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i}
      {q = ++-assoc Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm)}
      (core1Γ Γ Ξ₁ Γ₁ Δ₁ Δm)

  core1 : ∀ (Θ Γ Ξ₁ Γ₁ Δ₁ Δm : Ctx)
        → sym (β⊗-boundary (Θ ++ Γ ++ Ξ₁) Γ₁ Δ₁ Δm)
          ∙ ((λ i → flattenˡ Θ Γ Ξ₁ Γ₁ i ++ Δ₁ ++ Δm)
             ∙ (interchangeₘ-boundary Θ Γ (Ξ₁ ++ Γ₁) Δ₁ Δm
                ∙ (λ i → Θ ++ Γ ++ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i)))
        ≡ flattenˡ Θ Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm)
  core1 []      Γ Ξ₁ Γ₁ Δ₁ Δm = core1Γ Γ Ξ₁ Γ₁ Δ₁ Δm
  core1 (a ∷ Θ) Γ Ξ₁ Γ₁ Δ₁ Δm =
    ap-eq₄₁ (a ∷_)
      {p₁ = sym (β⊗-boundary (Θ ++ Γ ++ Ξ₁) Γ₁ Δ₁ Δm)}
      {p₂ = λ i → flattenˡ Θ Γ Ξ₁ Γ₁ i ++ Δ₁ ++ Δm}
      {p₃ = interchangeₘ-boundary Θ Γ (Ξ₁ ++ Γ₁) Δ₁ Δm}
      {p₄ = λ i → Θ ++ Γ ++ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i}
      {q = flattenˡ Θ Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm)}
      (core1 Θ Γ Ξ₁ Γ₁ Δ₁ Δm)

  -- Case: the ambient slot x sits in Γm.  plugˡ commutes g with the A-plug,
  -- sub-interchange commutes it with the B-plug, split-ββ carries the
  -- canonical split across β⊗-boundary, and co finishes.
  β⊗-L-case :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Ξ₁ : Ctx}
      (s₁ : Split x Θ Γm Ξ₁) (p : Ξ₁ ++ ((Γ₁ ++ Δ₁) ++ Δm) ≡ Ξ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ i → Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) (p i))
                  (split-++ˡ s₁ ((Γ₁ ++ Δ₁) ++ Δm)) s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → cast (flattenˡ Θ Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
        (match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} ⦅ M , N ⦆
          (cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
            (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) P g)))
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-L-case {x = x} {A = A} {B = B} {C = C} {Θ = Θ} {Ξ = Ξ} {Γ = Γ}
    {Γm = Γm} {Δm = Δm} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Ξ₁ = Ξ₁}
    s₁ p {s = s} co M N P g =
    ≈-trans
      (cast-≈ BIGᵒ (β⊗ {Γm = Θ ++ Γ ++ Ξ₁} {Δm = Δm} M N
        (cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
          (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) P g))))
      (pathp→≈ (tm-over α₁ Kchain))
    where
    apP  = ap (λ Ξ' → Θ ++ Γ ++ Ξ') p
    BIGᵒ = flattenˡ Θ Γ Ξ₁ ((Γ₁ ++ Δ₁) ++ Δm) ∙ apP
    P'   = cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
             (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) P g)
    SA   = split-here Γm A (B ∷ Δm)
    X₁   = sub SA P M
    X₂   = sub (split-++ʳ Γm (split-here Γ₁ B Δm)) X₁ N
    R    = cast (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂
    bb'  = β⊗-boundary (Θ ++ Γ ++ Ξ₁) Γ₁ Δ₁ Δm
    Y'   = sub (split-++ʳ (Θ ++ Γ ++ Ξ₁) (split-here Γ₁ B Δm))
             (sub (split-here (Θ ++ Γ ++ Ξ₁) A (B ∷ Δm)) P' M) N
    F₁c  = λ i → flattenˡ Θ Γ Ξ₁ Γ₁ i ++ Δ₁ ++ Δm
    IB₁  = interchangeₘ-boundary Θ Γ (Ξ₁ ++ Γ₁) Δ₁ Δm
    B4₁  = λ i → Θ ++ Γ ++ β⊗-boundary Ξ₁ Γ₁ Δ₁ Δm i

    E₂β : sub (split-++ˡ (split-here Θ x (Ξ₁ ++ Γ₁)) (Δ₁ ++ Δm))
            (sub (split-behind (split-++ˡ s₁ (Γ₁ ++ B ∷ Δm))
                               (split-++ʳ Ξ₁ (split-here Γ₁ B Δm))) X₁ N) g
        ≡ sub (split-++ˡ (split-++ˡ s₁ Γ₁) (Δ₁ ++ Δm)) X₂ g
    E₂β = sub-pathp {W = refl} {g = g} {g' = g}
            (λ i → split-++ˡ (split-canon (split-++ˡ s₁ Γ₁) i) (Δ₁ ++ Δm))
            (sub-pathp {W = refl} {t = X₁} {t' = X₁} {g = N} {g' = N}
              (behind-hereˡ s₁ Γ₁ Δm) refl refl)
            refl

    Kchain : PathP (λ i → Tm ((sym bb' ∙ (F₁c ∙ (IB₁ ∙ (B4₁ ∙ apP)))) i) C)
               (cast bb' Y') (sub s R g)
    Kchain =
      _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym bb'} {q = F₁c ∙ (IB₁ ∙ (B4₁ ∙ apP))}
        (symP (cast-filler bb' Y'))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = F₁c} {q = IB₁ ∙ (B4₁ ∙ apP)}
          (sub-pathp {W = refl} {g = N} {g' = N}
            (sq-++ʳ-flatten Θ Γ Ξ₁ (split-here Γ₁ B Δm))
            (plugˡ {y = A} {Δm = B ∷ Δm} s₁ P g M) refl)
          (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = IB₁} {q = B4₁ ∙ apP}
            (sub-interchange (split-++ˡ s₁ (Γ₁ ++ B ∷ Δm))
               (split-++ʳ Ξ₁ (split-here Γ₁ B Δm)) X₁ g N ▷ E₂β)
            (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B4₁} {q = apP}
              (sub-pathp {W = refl} {g = g} {g' = g}
                (split-ββ s₁ Γ₁ Δ₁ Δm)
                (cast-filler (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂) refl)
              (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                co refl refl))))

    α₁ : sym bb' ∙ (F₁c ∙ (IB₁ ∙ (B4₁ ∙ apP))) ≡ BIGᵒ
    α₁ = sh₄ (sym bb') F₁c IB₁ B4₁ apP
       ∙ ap (_∙ apP) (core1 Θ Γ Ξ₁ Γ₁ Δ₁ Δm)

  ap-eq₃₁ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d : X}
            {p₁ : a ≡ b} {p₂ : b ≡ c} {p₃ : c ≡ d} {q : a ≡ d}
          → p₁ ∙ (p₂ ∙ p₃) ≡ q
          → ap f p₁ ∙ (ap f p₂ ∙ ap f p₃) ≡ ap f q
  ap-eq₃₁ f {p₁ = p₁} {p₂ = p₂} {p₃ = p₃} eq =
    ap (ap f p₁ ∙_) (sym (ap-∙ f p₂ p₃))
    ∙ sym (ap-∙ f p₁ (p₂ ∙ p₃))
    ∙ ap (ap f) eq

  -- ++-assoc against flattenʳ (base: both reduce to refl).
  assoc-flatʳ : ∀ (Γm Θ₂ Γ Ξ : Ctx)
              → ++-assoc Γm Θ₂ (Γ ++ Ξ) ≡ sym (flattenʳ Γm Θ₂ Γ Ξ)
  assoc-flatʳ []       Θ₂ Γ Ξ = refl
  assoc-flatʳ (a ∷ Γm) Θ₂ Γ Ξ = ap (ap (a ∷_)) (assoc-flatʳ Γm Θ₂ Γ Ξ)

  -- split-behind through the binder pair, against the doubly weakened split
  -- (homogeneous: the prefixes agree definitionally).
  behind-⊗ : ∀ (Γm : Ctx) {x yA yB : Ty} {Θ₃ Δm Ξ : Ctx} (s₂ : Split x Θ₃ Δm Ξ)
           → split-behind (split-here Γm yA (yB ∷ Δm)) (split-++ʳ (yB ∷ []) s₂)
           ≡ split-++ʳ Γm (split-++ʳ (yA ∷ yB ∷ []) s₂)
  behind-⊗ []       s₂ = refl
  behind-⊗ (a ∷ Γm) s₂ = ap there (behind-⊗ Γm s₂)

  -- The canonical B-slot before the suffix-region reduction, against the
  -- one sub-interchange produces (base: split-here-++ˡ).
  sq-hereᵇ : ∀ (Γm Γ₁ : Ctx) {y : Ty} (Θ₃ Γ Ξ : Ctx)
           → PathP (λ i → Split y (Γm ++ Γ₁)
                                  (interchangeₘ-boundary Γm Γ₁ (y ∷ Θ₃) Γ Ξ i)
                                  (Θ₃ ++ Γ ++ Ξ))
               (split-++ˡ (split-++ʳ Γm (split-here Γ₁ y Θ₃)) (Γ ++ Ξ))
               (split-++ʳ Γm (split-here Γ₁ y (Θ₃ ++ Γ ++ Ξ)))
  sq-hereᵇ [] Γ₁ {y = y} Θ₃ Γ Ξ = split-here-++ˡ Γ₁ y Θ₃ (Γ ++ Ξ)
  sq-hereᵇ (a ∷ Γm) Γ₁ Θ₃ Γ Ξ i = there (sq-hereᵇ Γm Γ₁ Θ₃ Γ Ξ i)

  -- Reassociate the prefix of a doubly-buried slot (base is homogeneous).
  behind-hereʳ⊗ : ∀ (Γ₁ : Ctx) {x y : Ty} {Θ₃ Δm Ξ : Ctx} (s₂ : Split x Θ₃ Δm Ξ)
                → split-++ʳ Γ₁ (split-++ʳ (y ∷ []) s₂)
                ≡ split-behind (split-here Γ₁ y Δm) s₂
  behind-hereʳ⊗ []       s₂ = refl
  behind-hereʳ⊗ (a ∷ Γ₁) s₂ = ap there (behind-hereʳ⊗ Γ₁ s₂)

  behind-++ʳ-⊗ : ∀ (Γm Γ₁ : Ctx) {x y : Ty} {Θ₃ Δm Ξ : Ctx}
                 (s₂ : Split x Θ₃ Δm Ξ)
               → PathP (λ i → Split x (++-assoc Γm Γ₁ (y ∷ Θ₃) (~ i))
                                      (Γm ++ Γ₁ ++ y ∷ Δm) Ξ)
                   (split-++ʳ Γm (split-++ʳ Γ₁ (split-++ʳ (y ∷ []) s₂)))
                   (split-behind (split-++ʳ Γm (split-here Γ₁ y Δm)) s₂)
  behind-++ʳ-⊗ []       Γ₁ s₂ = behind-hereʳ⊗ Γ₁ s₂
  behind-++ʳ-⊗ (a ∷ Γm) Γ₁ s₂ i = there (behind-++ʳ-⊗ Γm Γ₁ s₂ i)

  -- The slot sits in Δm: the canonical x-split across β⊗-boundary (the
  -- prefix line is β⊗-boundary at Θ₃).
  split-ββ³ : ∀ (Γm : Ctx) {x : Ty} {Θ₃ Δm Ξ : Ctx}
              (s₂ : Split x Θ₃ Δm Ξ) (Γ₁ Δ₁ : Ctx)
            → PathP (λ i → Split x (β⊗-boundary Γm Γ₁ Δ₁ Θ₃ i)
                                   (β⊗-boundary Γm Γ₁ Δ₁ Δm i) Ξ)
                (split-++ʳ (Γm ++ Γ₁) (split-++ʳ Δ₁ s₂))
                (split-++ʳ Γm (split-++ʳ (Γ₁ ++ Δ₁) s₂))
  split-ββ³ []       s₂ Γ₁ Δ₁ = symP (split-++ʳ-++ Γ₁ Δ₁ s₂)
  split-ββ³ (a ∷ Γm) s₂ Γ₁ Δ₁ i = there (split-ββ³ Γm s₂ Γ₁ Δ₁ i)

  -- Core coherence for the Δm-region, Γ₁-level (Γm = []).
  core3Γ : ∀ (Γ₁ Δ₁ Θ₃ Γ Ξ : Ctx)
         → ++-assoc Γ₁ Δ₁ (Θ₃ ++ Γ ++ Ξ)
           ∙ (sym (interchangeₘ-boundary Γ₁ Δ₁ Θ₃ Γ Ξ)
              ∙ ap (_++ Γ ++ Ξ) (sym (++-assoc Γ₁ Δ₁ Θ₃)))
         ≡ sym (++-assoc (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ))
  core3Γ [] Δ₁ Θ₃ Γ Ξ =
      ∙-idl (sym (++-assoc Δ₁ Θ₃ (Γ ++ Ξ)) ∙ refl)
    ∙ ∙-idr (sym (++-assoc Δ₁ Θ₃ (Γ ++ Ξ)))
  core3Γ (a ∷ Γ₁) Δ₁ Θ₃ Γ Ξ =
    ap-eq₃₁ (a ∷_)
      {p₁ = ++-assoc Γ₁ Δ₁ (Θ₃ ++ Γ ++ Ξ)}
      {p₂ = sym (interchangeₘ-boundary Γ₁ Δ₁ Θ₃ Γ Ξ)}
      {p₃ = ap (_++ Γ ++ Ξ) (sym (++-assoc Γ₁ Δ₁ Θ₃))}
      {q = sym (++-assoc (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ))}
      (core3Γ Γ₁ Δ₁ Θ₃ Γ Ξ)

  core3 : ∀ (Γm Γ₁ Δ₁ Θ₃ Γ Ξ : Ctx)
        → sym (β⊗-boundary Γm Γ₁ Δ₁ (Θ₃ ++ Γ ++ Ξ))
          ∙ (sym (interchangeₘ-boundary (Γm ++ Γ₁) Δ₁ Θ₃ Γ Ξ)
             ∙ (λ i → β⊗-boundary Γm Γ₁ Δ₁ Θ₃ i ++ Γ ++ Ξ))
        ≡ bury Γm (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ)
  core3 []       Γ₁ Δ₁ Θ₃ Γ Ξ = core3Γ Γ₁ Δ₁ Θ₃ Γ Ξ
  core3 (a ∷ Γm) Γ₁ Δ₁ Θ₃ Γ Ξ =
    ap-eq₃₁ (a ∷_)
      {p₁ = sym (β⊗-boundary Γm Γ₁ Δ₁ (Θ₃ ++ Γ ++ Ξ))}
      {p₂ = sym (interchangeₘ-boundary (Γm ++ Γ₁) Δ₁ Θ₃ Γ Ξ)}
      {p₃ = λ i → β⊗-boundary Γm Γ₁ Δ₁ Θ₃ i ++ Γ ++ Ξ}
      {q = bury Γm (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ)}
      (core3 Γm Γ₁ Δ₁ Θ₃ Γ Ξ)

  -- Case: the ambient slot x sits in Δm.  Two interchanges read
  -- right-to-left (g is behind both the A- and the B-plug), the boundary
  -- split-line, and the two view soundness squares.
  β⊗-R-case :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Θ₂ Θ₃ : Ctx}
      (s₂' : Split x Θ₃ Δm Ξ) (q₂ : (Γ₁ ++ Δ₁) ++ Θ₃ ≡ Θ₂)
      {s' : Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co₂ : PathP (λ i → Split x (q₂ i) ((Γ₁ ++ Δ₁) ++ Δm) Ξ)
                   (split-++ʳ (Γ₁ ++ Δ₁) s₂') s')
      (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → cast (bury Γm (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ)
            ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
        (match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} ⦅ M , N ⦆
          (cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
            (sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂')) P g)))
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-R-case {x = x} {A = A} {B = B} {C = C} {Θ = Θ} {Ξ = Ξ} {Γ = Γ}
    {Γm = Γm} {Δm = Δm} {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Θ₂ = Θ₂} {Θ₃ = Θ₃}
    s₂' q₂ {s' = s'} co₂ q {s = s} co M N P g =
    ≈-trans
      (cast-≈ BIG₃ (β⊗ {Γm = Γm} {Δm = Θ₃ ++ Γ ++ Ξ} M N P*))
      (pathp→≈ (tm-over α₃ Kchain))
    where
    BIG₃ = bury Γm (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ)
           ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q)
    P*   = cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
             (sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂')) P g)
    SA₃  = split-here Γm A (B ∷ (Θ₃ ++ Γ ++ Ξ))
    SB₃  = split-++ʳ Γm (split-here Γ₁ B (Θ₃ ++ Γ ++ Ξ))
    SB   = split-++ʳ Γm (split-here Γ₁ B Δm)
    X₁   = sub (split-here Γm A (B ∷ Δm)) P M
    X₂   = sub SB X₁ N
    R    = cast (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂
    bb₃  = β⊗-boundary Γm Γ₁ Δ₁ (Θ₃ ++ Γ ++ Ξ)
    Y₃   = sub SB₃ (sub SA₃ P* M) N
    IB₃  = interchangeₘ-boundary (Γm ++ Γ₁) Δ₁ Θ₃ Γ Ξ
    B5₃  = λ i → β⊗-boundary Γm Γ₁ Δ₁ Θ₃ i ++ Γ ++ Ξ
    B6₃  = λ i → (Γm ++ q₂ i) ++ Γ ++ Ξ
    B7₃  = λ i → q i ++ Γ ++ Ξ
    P*'  = cast (++-assoc Γm (A ∷ B ∷ Θ₃) (Γ ++ Ξ))
             (sub (split-behind (split-here Γm A (B ∷ Δm)) (split-++ʳ (B ∷ []) s₂')) P g)

    r2 : Y₃ ≡ sub SB₃ (sub SA₃ P*' M) N
    r2 j = sub SB₃ (sub SA₃
             (cast (sym (assoc-flatʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ) j)
               (sub (sym (behind-⊗ Γm s₂') j) P g)) M) N

    r3 : sub SB₃ (sub SA₃ P*' M) N
       ≡ sub (split-++ˡ (split-++ʳ Γm (split-here Γ₁ B Θ₃)) (Γ ++ Ξ))
           (sub (split-++ʳ Γm (split-++ʳ Γ₁ (split-++ʳ (B ∷ []) s₂'))) X₁ g) N
    r3 = sub-pathp {W = refl} {g = N} {g' = N}
           (symP (sq-hereᵇ Γm Γ₁ Θ₃ Γ Ξ))
           (symP (plugʳ {y = A} {Δm = B ∷ Δm} (split-++ʳ (B ∷ []) s₂') P g M))
           refl

    r4pre : sub (split-++ˡ (split-++ʳ Γm (split-here Γ₁ B Θ₃)) (Γ ++ Ξ))
              (sub (split-++ʳ Γm (split-++ʳ Γ₁ (split-++ʳ (B ∷ []) s₂'))) X₁ g) N
          ≡ sub (split-++ˡ (split-here (Γm ++ Γ₁) B Θ₃) (Γ ++ Ξ))
              (sub (split-behind SB s₂') X₁ g) N
    r4pre = sub-pathp {W = refl} {g = N} {g' = N}
              (λ i → split-++ˡ (split-here-++ʳ Γm Γ₁ B Θ₃ i) (Γ ++ Ξ))
              (sub-pathp {W = refl} {t = X₁} {t' = X₁} {g = g} {g' = g}
                (behind-++ʳ-⊗ Γm Γ₁ s₂') refl refl)
              refl

    Kchain : PathP (λ i → Tm ((sym bb₃ ∙ (sym IB₃ ∙ (B5₃ ∙ (B6₃ ∙ B7₃)))) i) C)
               (cast bb₃ Y₃) (sub s R g)
    Kchain =
      _∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym bb₃} {q = sym IB₃ ∙ (B5₃ ∙ (B6₃ ∙ B7₃))}
        (symP (cast-filler bb₃ Y₃) ▷ (r2 ∙ r3 ∙ r4pre))
        (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = sym IB₃} {q = B5₃ ∙ (B6₃ ∙ B7₃)}
          (symP (sub-interchange SB s₂' X₁ N g))
          (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B5₃} {q = B6₃ ∙ B7₃}
            (sub-pathp {W = refl} {g = g} {g' = g}
              (split-ββ³ Γm s₂' Γ₁ Δ₁)
              (cast-filler (β⊗-boundary Γm Γ₁ Δ₁ Δm) X₂) refl)
            (_∙P_ {B = λ Ρ' → Tm Ρ' C} {p = B6₃} {q = B7₃}
              (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                (λ i → split-++ʳ Γm (co₂ i)) refl refl)
              (sub-pathp {W = refl} {t = R} {t' = R} {g = g} {g' = g}
                co refl refl))))

    α₃ : sym bb₃ ∙ (sym IB₃ ∙ (B5₃ ∙ (B6₃ ∙ B7₃))) ≡ BIG₃
    α₃ = sh₃ (sym bb₃) (sym IB₃) B5₃ (B6₃ ∙ B7₃)
       ∙ ap (_∙ (B6₃ ∙ B7₃)) (core3 Γm Γ₁ Δ₁ Θ₃ Γ Ξ)
       ∙ ap (bury Γm (Γ₁ ++ Δ₁) Θ₃ (Γ ++ Ξ) ∙_)
            (sym (ap-∙ (_++ Γ ++ Ξ) (ap (Γm ++_) q₂) q))

  -- Dispatchers: match the views so each case reduces definitionally.
  β⊗-handler-pair :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Θ₂ Ξ₁' : Ctx}
      {s₁' : Split x Θ₂ (Γ₁ ++ Δ₁) Ξ₁'}
      (v₃ : Split-++ Γ₁ Δ₁ s₁')
      (p' : Ξ₁' ++ Δm ≡ Ξ)
      {s' : Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co' : PathP (λ i → Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) (p' i)) (split-++ˡ s₁' Δm) s')
      (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → cast (flattenᵐ Γm Θ₂ Γ Ξ₁' Δm ∙ (λ i → q i ++ Γ ++ p' i))
        (match⊗ {Γ = Γm} {Δ = Δm} (sub-pair v₃ M N g) P)
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-handler-pair (on-left s₁'' p'' co'') p' co' q co M N P g =
    β⊗-pairL-case s₁'' p'' co'' p' co' q co M N P g
  β⊗-handler-pair (on-right s₂'' q'' co'') p' co' q co M N P g =
    β⊗-pairR-case s₂'' q'' co'' p' co' q co M N P g

  β⊗-handlerʳ :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ Θ₂ : Ctx}
      {s' : Split x Θ₂ ((Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (v : Split-++ (Γ₁ ++ Δ₁) Δm s') (q : Γm ++ Θ₂ ≡ Θ)
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (co : PathP (λ k → Split x (q k) (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ) (split-++ʳ Γm s') s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → sub-match⊗ʳ v q ⦅ M , N ⦆ P g
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-handlerʳ {Γ₁ = Γ₁} (on-left {Ξ₁ = Ξ₁'} s₁' p' co') q co M N P g =
    β⊗-handler-pair (split-++ Γ₁ s₁') p' co' q co M N P g
  β⊗-handlerʳ (on-right {Θ₂ = Θ₃} s₂' q₂ co₂) q co M N P g =
    β⊗-R-case s₂' q₂ co₂ q co M N P g

  β⊗-handler :
    ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ : Ctx}
      {s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ}
      (v : Split-++ Γm ((Γ₁ ++ Δ₁) ++ Δm) s)
      (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    → sub-match⊗ˡ v ⦅ M , N ⦆ P g
    ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
        (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
          (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
  β⊗-handler (on-left {Ξ₁ = Ξ₁} s₁ p co) M N P g =
    β⊗-L-case s₁ p co M N P g
  β⊗-handler {Γ₁ = Γ₁} {Δ₁ = Δ₁} (on-right s' q co) M N P g =
    β⊗-handlerʳ (split-++ (Γ₁ ++ Δ₁) s') q co M N P g

β⊗-sub : ∀ {x A B C : Ty} {Θ Ξ Γ Γm Δm Γ₁ Δ₁ : Ctx}
         (s : Split x Θ (Γm ++ (Γ₁ ++ Δ₁) ++ Δm) Ξ)
         (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
       → sub s (match⊗ {Γ = Γm} {Δ = Δm} ⦅ M , N ⦆ P) g
       ≈ sub s (cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
           (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
             (sub (split-here Γm A (B ∷ Δm)) P M) N)) g
β⊗-sub {Γm = Γm} s M N P g = β⊗-handler (split-++ Γm s) M N P g
