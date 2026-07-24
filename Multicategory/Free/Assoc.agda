open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
open import Multicategory.Free

module Multicategory.Free.Assoc {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G

-- Associativity of substitution (Shulman's Lemma 2.4.9, associativity
-- half): plugging h into the slot inherited from g commutes with plugging
-- g into t.  Architecture: mutual induction on the term at handler
-- granularity (one lemma per sub branch handler, matching the Split-++
-- view so the inner sub reduces), with the outer sub carried across the
-- handler's cast via sub-pathp, the IH applied under the constructor, and
-- the residual base-path discrepancy closed by tm-over/sp-over along
-- path-of-paths squares proved by structural list induction.

private variable
  x y z a A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Λ Μ Κ Γ₁ Γ₂ Δ₁ Ξ₁ Θ₂ Φ : Ctx
  As : List (Multigraph.Ob G)

-- ==========================================================================
-- PathP composition over composite base paths (comp over ∙-filler), for
-- Tm, Sp and Split.  These let us chain heterogeneous segments and
-- reconcile the ∙-composite base once at the end.
-- ==========================================================================

private
  tm-∙P : {P : Γ ≡ Δ} {Q : Δ ≡ Ρ} {t : Tm Γ z} {t' : Tm Δ z} {t'' : Tm Ρ z}
        → PathP (λ i → Tm (P i) z) t t'
        → PathP (λ i → Tm (Q i) z) t' t''
        → PathP (λ i → Tm ((P ∙ Q) i) z) t t''
  tm-∙P {z = z} {P = P} {Q = Q} {t = t} {t' = t'} {t'' = t''} p q i =
    comp (λ j → Tm (∙-filler P Q j i) z) (∂ i) λ where
      j (j = i0) → p i
      j (i = i0) → t
      j (i = i1) → q j

  sp-∙P : {P : Γ ≡ Δ} {Q : Δ ≡ Ρ} {ts : Sp Γ As} {ts' : Sp Δ As} {ts'' : Sp Ρ As}
        → PathP (λ i → Sp (P i) As) ts ts'
        → PathP (λ i → Sp (Q i) As) ts' ts''
        → PathP (λ i → Sp ((P ∙ Q) i) As) ts ts''
  sp-∙P {As = As} {P = P} {Q = Q} {ts = ts} {ts' = ts'} {ts'' = ts''} p q i =
    comp (λ j → Sp (∙-filler P Q j i) As) (∂ i) λ where
      j (j = i0) → p i
      j (i = i0) → ts
      j (i = i1) → q j

  split-∙P : {Θ' Θ'' Ξ' Ξ'' Ρ' Ρ'' : Ctx}
             {P : Θ ≡ Θ'} {P' : Θ' ≡ Θ''} {Q : Ξ ≡ Ξ'} {Q' : Ξ' ≡ Ξ''}
             {R : Ρ ≡ Ρ'} {R' : Ρ' ≡ Ρ''}
             {s₀ : Split x Θ Ρ Ξ} {s₁ : Split x Θ' Ρ' Ξ'} {s₂ : Split x Θ'' Ρ'' Ξ''}
           → PathP (λ i → Split x (P i) (R i) (Q i)) s₀ s₁
           → PathP (λ i → Split x (P' i) (R' i) (Q' i)) s₁ s₂
           → PathP (λ i → Split x ((P ∙ P') i) ((R ∙ R') i) ((Q ∙ Q') i)) s₀ s₂
  split-∙P {x = x} {P = P} {P' = P'} {Q = Q} {Q' = Q'} {R = R} {R' = R'}
           {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} p q i =
    comp (λ j → Split x (∙-filler P P' j i) (∙-filler R R' j i) (∙-filler Q Q' j i))
         (∂ i) λ where
      j (j = i0) → p i
      j (i = i0) → s₀
      j (i = i1) → q j

-- ==========================================================================
-- One-dimensional path algebra.  All chains below are nested as
-- a ∙ ((b ∙ c) ∙ d) (one leading segment, a bracketed core, one trailing
-- segment), so a single ap-distribution shape covers every cons step of the
-- base-path squares.
-- ==========================================================================

private
  ∙-ap₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {v w x' : X}
          (p : v ≡ w) (q : w ≡ x')
        → ap f p ∙ ap f q ≡ ap f (p ∙ q)
  ∙-ap₂ f p q = sym (ap-∙ f p q)

  -- Push a composite equation under an ap (cons step for two-segment chains).
  ap-∙-step : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c : X}
              {p : a ≡ b} {q : b ≡ c} {r : a ≡ c}
            → p ∙ q ≡ r → ap f p ∙ ap f q ≡ ap f r
  ap-∙-step f {p = p} {q = q} eq = ∙-ap₂ f p q ∙ ap (ap f) eq

  -- The four-segment shape: cons step of every big square below.
  ∙-ap-sh : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {v w x' y' z' : X}
            (a : v ≡ w) (b : w ≡ x') (c : x' ≡ y') (d : y' ≡ z')
          → ap f a ∙ ((ap f b ∙ ap f c) ∙ ap f d)
          ≡ ap f (a ∙ ((b ∙ c) ∙ d))
  ∙-ap-sh f a b c d =
      ap (ap f a ∙_) (ap (_∙ ap f d) (∙-ap₂ f b c) ∙ ∙-ap₂ f (b ∙ c) d)
    ∙ ∙-ap₂ f a ((b ∙ c) ∙ d)

  -- Cons step packaged: distribute the ap, then apply the IH.  The four
  -- segment paths are explicit — the ∙'s in the inferred type are hcomps,
  -- so Agda cannot recover them from the IH alone.
  sq-step : ∀ (a : Ty) {v w x' y' z' : Ctx}
            (p : v ≡ w) (q : w ≡ x') (r : x' ≡ y') (s : y' ≡ z') {t : v ≡ z'}
          → p ∙ ((q ∙ r) ∙ s) ≡ t
          → ap (a ∷_) p ∙ ((ap (a ∷_) q ∙ ap (a ∷_) r) ∙ ap (a ∷_) s)
          ≡ ap (a ∷_) t
  sq-step a p q r s eq =
    ∙-ap-sh (a ∷_) p q r s ∙ ap (ap (a ∷_)) eq

  -- Collapse the ∙ refl left over by a view computation's p/q component.
  cast-∙idr : ∀ {z' : Ty} {Ρ' Γ' : Ctx} (p : Ρ' ≡ Γ') (t : Tm Ρ' z')
            → cast (p ∙ refl) t ≡ cast p t
  cast-∙idr p t = ap (λ ρ → cast ρ t) (∙-idr p)

  sp-cast-∙idr : ∀ {As' : List (Multigraph.Ob G)} {Ρ' Γ' : Ctx}
                 (p : Ρ' ≡ Γ') (ts : Sp Ρ' As')
               → sp-cast (p ∙ refl) ts ≡ sp-cast p ts
  sp-cast-∙idr p ts = ap (λ ρ → sp-cast ρ ts) (∙-idr p)

-- ==========================================================================
-- Split co-squares: the outer split (the y-slot, riding inside g's context
-- Λ) pushed through each handler's reassociation cast.  All cons-by-cons;
-- bases delegate to the SplitLemmas coherences.
-- ==========================================================================

-- Over flattenˡ: suffix weakening of the buried y-slot fuses.
co-L : ∀ (Θ : Ctx) {y : Ty} {Φ Λ Ψ : Ctx} (s' : Split y Φ Λ Ψ) (Ξ₁ Δ₁ : Ctx)
     → PathP (λ i → Split y (Θ ++ Φ) (flattenˡ Θ Λ Ξ₁ Δ₁ i) (++-assoc Ψ Ξ₁ Δ₁ i))
         (split-++ˡ (split-++ʳ Θ (split-++ˡ s' Ξ₁)) Δ₁)
         (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁)))
co-L []      s' Ξ₁ Δ₁ = split-++ˡ-++ s' Ξ₁ Δ₁
co-L (a ∷ Θ) s' Ξ₁ Δ₁ i = there (co-L Θ s' Ξ₁ Δ₁ i)

-- Over flattenʳ: prefix burials of the y-slot reassociate.
co-R : ∀ (Γ₁ Θ₂ : Ctx) {y : Ty} {Φ Λ Ψ : Ctx} (s' : Split y Φ Λ Ψ) (Ξ : Ctx)
     → PathP (λ i → Split y (sym (++-assoc Γ₁ Θ₂ Φ) i)
                            (flattenʳ Γ₁ Θ₂ Λ Ξ i) (Ψ ++ Ξ))
         (split-++ʳ Γ₁ (split-++ʳ Θ₂ (split-++ˡ s' Ξ)))
         (split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ))
co-R []       Θ₂ s' Ξ = refl
co-R (a ∷ Γ₁) Θ₂ s' Ξ i = there (co-R Γ₁ Θ₂ s' Ξ i)

-- Over flattenᵐ: the y-slot buried in the middle region.
co-M : ∀ (Γm Θ₂ : Ctx) {y : Ty} {Φ Λ Ψ : Ctx} (s' : Split y Φ Λ Ψ) (Ξ₁ Δm : Ctx)
     → PathP (λ i → Split y (sym (++-assoc Γm Θ₂ Φ) i)
                            (flattenᵐ Γm Θ₂ Λ Ξ₁ Δm i) (++-assoc Ψ Ξ₁ Δm i))
         (split-++ʳ Γm (split-++ˡ (split-++ʳ Θ₂ (split-++ˡ s' Ξ₁)) Δm))
         (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm)))
co-M []       Θ₂ s' Ξ₁ Δm = co-L Θ₂ s' Ξ₁ Δm
co-M (a ∷ Γm) Θ₂ s' Ξ₁ Δm i = there (co-M Γm Θ₂ s' Ξ₁ Δm i)

-- Over bury: the y-slot buried in the last region, under two prefixes.
co-B : ∀ (Γm Ψm Θ₃ : Ctx) {y : Ty} {Φ Λ Ψ : Ctx} (s' : Split y Φ Λ Ψ) (Ξ : Ctx)
     → PathP (λ i → Split y (bury Γm Ψm Θ₃ Φ i)
                            (bury Γm Ψm Θ₃ (Λ ++ Ξ) i) (Ψ ++ Ξ))
         (split-++ʳ Γm (split-++ʳ Ψm (split-++ʳ Θ₃ (split-++ˡ s' Ξ))))
         (split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ))
co-B []       Ψm Θ₃ s' Ξ = symP (split-++ʳ-++ Ψm Θ₃ (split-++ˡ s' Ξ))
co-B (a ∷ Γm) Ψm Θ₃ s' Ξ i = there (co-B Γm Ψm Θ₃ s' Ξ i)

-- ==========================================================================
-- Base-path squares.  Each reconciles the a ∙ ((b ∙ c) ∙ d) composite of a
-- core's segment base paths against the target assocₘ-boundary.  Structural
-- list inductions; cons steps are sq-step, bases are groupoid algebra.
-- ==========================================================================

private
  -- Square for the on-left cores, innermost level (Θ = [], Φ = []).
  sq-LΜ : ∀ (Μ Ψ Ξ₁ Δ₁ : Ctx)
    → sym (ap (λ l → Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁))
      ∙ ((sym (flattenˡ [] Μ (Ψ ++ Ξ₁) Δ₁)
          ∙ ap (_++ Δ₁) (sym (++-assoc Μ Ψ Ξ₁)))
         ∙ ++-assoc (Μ ++ Ψ) Ξ₁ Δ₁)
    ≡ sym (++-assoc Μ Ψ (Ξ₁ ++ Δ₁))
  sq-LΜ [] Ψ Ξ₁ Δ₁ =
      ap (sym (++-assoc Ψ Ξ₁ Δ₁) ∙_)
         (ap (_∙ ++-assoc Ψ Ξ₁ Δ₁) (∙-idl refl) ∙ ∙-idl (++-assoc Ψ Ξ₁ Δ₁))
    ∙ ∙-invl (++-assoc Ψ Ξ₁ Δ₁)
  sq-LΜ (a ∷ Μ) Ψ Ξ₁ Δ₁ =
    sq-step a
      (sym (ap (λ l → Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁)))
      (sym (flattenˡ [] Μ (Ψ ++ Ξ₁) Δ₁))
      (ap (_++ Δ₁) (sym (++-assoc Μ Ψ Ξ₁)))
      (++-assoc (Μ ++ Ψ) Ξ₁ Δ₁)
      (sq-LΜ Μ Ψ Ξ₁ Δ₁)

  -- Θ = [] level of sq-L.
  sq-LΦ : ∀ (Φ Μ Ψ Ξ₁ Δ₁ : Ctx)
    → sym (ap (λ l → Φ ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁))
      ∙ ((sym (flattenˡ Φ Μ (Ψ ++ Ξ₁) Δ₁)
          ∙ ap (_++ Δ₁) (assocₘ-flatten Φ Μ Ψ Ξ₁))
         ∙ ++-assoc (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁)
    ≡ assocₘ-flatten Φ Μ Ψ (Ξ₁ ++ Δ₁)
  sq-LΦ []      Μ Ψ Ξ₁ Δ₁ = sq-LΜ Μ Ψ Ξ₁ Δ₁
  sq-LΦ (a ∷ Φ) Μ Ψ Ξ₁ Δ₁ =
    sq-step a
      (sym (ap (λ l → Φ ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁)))
      (sym (flattenˡ Φ Μ (Ψ ++ Ξ₁) Δ₁))
      (ap (_++ Δ₁) (assocₘ-flatten Φ Μ Ψ Ξ₁))
      (++-assoc (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁)
      (sq-LΦ Φ Μ Ψ Ξ₁ Δ₁)

  -- Square for the on-left cores (pair, cons, and the outer layer of the
  -- match on-left cores, with Δ₁ instantiated to the trailing region).
  sq-L : ∀ (Θ Φ Μ Ψ Ξ₁ Δ₁ : Ctx)
    → sym (ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁))
      ∙ ((sym (flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) Δ₁)
          ∙ ap (_++ Δ₁) (assocₘ-boundary Θ Φ Μ Ψ Ξ₁))
         ∙ flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁)
    ≡ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δ₁)
  sq-L []      Φ Μ Ψ Ξ₁ Δ₁ = sq-LΦ Φ Μ Ψ Ξ₁ Δ₁
  sq-L (a ∷ Θ) Φ Μ Ψ Ξ₁ Δ₁ =
    sq-step a
      (sym (ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δ₁)))
      (sym (flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) Δ₁))
      (ap (_++ Δ₁) (assocₘ-boundary Θ Φ Μ Ψ Ξ₁))
      (flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁)
      (sq-L Θ Φ Μ Ψ Ξ₁ Δ₁)

  -- Square for the var case (two segments only).
  var-α₀ : ∀ (Μ' Ψ : Ctx)
    → (λ i → Μ' ++ ++-idr Ψ i) ∙ sym (++-idr (Μ' ++ Ψ))
    ≡ sym (++-assoc Μ' Ψ [])
  var-α₀ []       Ψ = ∙-invr (++-idr Ψ)
  var-α₀ (a ∷ Μ') Ψ =
    ap-∙-step (a ∷_)
      {p = λ i → Μ' ++ ++-idr Ψ i} {q = sym (++-idr (Μ' ++ Ψ))}
      (var-α₀ Μ' Ψ)

  var-α : ∀ (Φ Μ' Ψ : Ctx)
    → (λ i → Φ ++ Μ' ++ ++-idr Ψ i) ∙ sym (++-idr (Φ ++ Μ' ++ Ψ))
    ≡ assocₘ-flatten Φ Μ' Ψ []
  var-α []      Μ' Ψ = var-α₀ Μ' Ψ
  var-α (a ∷ Φ) Μ' Ψ =
    ap-∙-step (a ∷_)
      {p = λ i → Φ ++ Μ' ++ ++-idr Ψ i} {q = sym (++-idr (Φ ++ Μ' ++ Ψ))}
      (var-α Φ Μ' Ψ)

private
  -- Shared groupoid base: the degenerate square with three refl segments.
  sq-base : ∀ {ℓ} {X : Type ℓ} {u v : X} (p : u ≡ v)
          → refl ∙ ((refl ∙ p) ∙ refl) ≡ p
  sq-base p = ∙-idl _ ∙ ∙-idr _ ∙ ∙-idl p

  -- Square for the on-right cores (pair, cons).
  sq-R : ∀ (Γ₁ Θ₂ Φ Μ Ψ Ξ : Ctx)
    → ap (_++ Μ ++ Ψ ++ Ξ) (++-assoc Γ₁ Θ₂ Φ)
      ∙ ((sym (flattenʳ Γ₁ (Θ₂ ++ Φ) Μ (Ψ ++ Ξ))
          ∙ ap (Γ₁ ++_) (assocₘ-boundary Θ₂ Φ Μ Ψ Ξ))
         ∙ flattenʳ Γ₁ Θ₂ (Φ ++ Μ ++ Ψ) Ξ)
    ≡ assocₘ-boundary (Γ₁ ++ Θ₂) Φ Μ Ψ Ξ
  sq-R []       Θ₂ Φ Μ Ψ Ξ = sq-base (assocₘ-boundary Θ₂ Φ Μ Ψ Ξ)
  sq-R (a ∷ Γ₁) Θ₂ Φ Μ Ψ Ξ =
    sq-step a
      (ap (_++ Μ ++ Ψ ++ Ξ) (++-assoc Γ₁ Θ₂ Φ))
      (sym (flattenʳ Γ₁ (Θ₂ ++ Φ) Μ (Ψ ++ Ξ)))
      (ap (Γ₁ ++_) (assocₘ-boundary Θ₂ Φ Μ Ψ Ξ))
      (flattenʳ Γ₁ Θ₂ (Φ ++ Μ ++ Ψ) Ξ)
      (sq-R Γ₁ Θ₂ Φ Μ Ψ Ξ)

  -- Square for the match ʳ/on-left cores (slot in the middle region).
  sq-M : ∀ (Γm Θ₂ Φ Μ Ψ Ξ₁ Δm : Ctx)
    → sym (λ i → sym (++-assoc Γm Θ₂ Φ) i ++ Μ ++ ++-assoc Ψ Ξ₁ Δm i)
      ∙ ((sym (flattenᵐ Γm (Θ₂ ++ Φ) Μ (Ψ ++ Ξ₁) Δm)
          ∙ ap (λ l → Γm ++ l ++ Δm) (assocₘ-boundary Θ₂ Φ Μ Ψ Ξ₁))
         ∙ flattenᵐ Γm Θ₂ (Φ ++ Μ ++ Ψ) Ξ₁ Δm)
    ≡ assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ (Ξ₁ ++ Δm)
  sq-M []       Θ₂ Φ Μ Ψ Ξ₁ Δm = sq-L Θ₂ Φ Μ Ψ Ξ₁ Δm
  sq-M (a ∷ Γm) Θ₂ Φ Μ Ψ Ξ₁ Δm =
    sq-step a
      (sym (λ i → sym (++-assoc Γm Θ₂ Φ) i ++ Μ ++ ++-assoc Ψ Ξ₁ Δm i))
      (sym (flattenᵐ Γm (Θ₂ ++ Φ) Μ (Ψ ++ Ξ₁) Δm))
      (ap (λ l → Γm ++ l ++ Δm) (assocₘ-boundary Θ₂ Φ Μ Ψ Ξ₁))
      (flattenᵐ Γm Θ₂ (Φ ++ Μ ++ Ψ) Ξ₁ Δm)
      (sq-M Γm Θ₂ Φ Μ Ψ Ξ₁ Δm)

  -- Square for the match ʳ/on-right cores (slot in the last region),
  -- Γm = [] level first.
  sq-BΨ : ∀ (Ψm Θ₃ Φ Μ Ψ Ξ : Ctx)
    → sym (λ i → sym (++-assoc Ψm Θ₃ Φ) i ++ Μ ++ Ψ ++ Ξ)
      ∙ ((++-assoc Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ)
          ∙ ap (λ l → Ψm ++ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ))
         ∙ sym (++-assoc Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ)))
    ≡ assocₘ-boundary (Ψm ++ Θ₃) Φ Μ Ψ Ξ
  sq-BΨ []       Θ₃ Φ Μ Ψ Ξ = sq-base (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ)
  sq-BΨ (a ∷ Ψm) Θ₃ Φ Μ Ψ Ξ =
    sq-step a
      (sym (λ i → sym (++-assoc Ψm Θ₃ Φ) i ++ Μ ++ Ψ ++ Ξ))
      (++-assoc Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ))
      (ap (λ l → Ψm ++ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ))
      (sym (++-assoc Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ)))
      (sq-BΨ Ψm Θ₃ Φ Μ Ψ Ξ)

  sq-B : ∀ (Γm Ψm Θ₃ Φ Μ Ψ Ξ : Ctx)
    → sym (λ i → bury Γm Ψm Θ₃ Φ i ++ Μ ++ Ψ ++ Ξ)
      ∙ ((sym (bury Γm Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ))
          ∙ ap (λ l → Γm ++ Ψm ++ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ))
         ∙ bury Γm Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ))
    ≡ assocₘ-boundary (Γm ++ Ψm ++ Θ₃) Φ Μ Ψ Ξ
  sq-B []       Ψm Θ₃ Φ Μ Ψ Ξ = sq-BΨ Ψm Θ₃ Φ Μ Ψ Ξ
  sq-B (a ∷ Γm) Ψm Θ₃ Φ Μ Ψ Ξ =
    sq-step a
      (sym (λ i → bury Γm Ψm Θ₃ Φ i ++ Μ ++ Ψ ++ Ξ))
      (sym (bury Γm Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ)))
      (ap (λ l → Γm ++ Ψm ++ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ))
      (bury Γm Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ))
      (sq-B Γm Ψm Θ₃ Φ Μ Ψ Ξ)

private
  -- Inner square for the match on-left cores: the under-the-binder segment
  -- against the ap (_++ D) image of the outer boundary (D is the binder
  -- extension A ∷ B ∷ Δm, resp. Δm).  Three-level induction.
  sq-L-innerΜ : ∀ (Μ Ψ Ξ₁ D : Ctx)
    → ++-assoc Μ (Ψ ++ Ξ₁) D
      ∙ ((ap (λ l → Μ ++ l) (++-assoc Ψ Ξ₁ D)
          ∙ sym (++-assoc Μ Ψ (Ξ₁ ++ D)))
         ∙ sym (++-assoc (Μ ++ Ψ) Ξ₁ D))
    ≡ ap (_++ D) (sym (++-assoc Μ Ψ Ξ₁))
  sq-L-innerΜ [] Ψ Ξ₁ D =
      ∙-idl _
    ∙ ap (_∙ sym (++-assoc Ψ Ξ₁ D)) (∙-idr (++-assoc Ψ Ξ₁ D))
    ∙ ∙-invr (++-assoc Ψ Ξ₁ D)
  sq-L-innerΜ (a ∷ Μ) Ψ Ξ₁ D =
    sq-step a
      (++-assoc Μ (Ψ ++ Ξ₁) D)
      (ap (λ l → Μ ++ l) (++-assoc Ψ Ξ₁ D))
      (sym (++-assoc Μ Ψ (Ξ₁ ++ D)))
      (sym (++-assoc (Μ ++ Ψ) Ξ₁ D))
      (sq-L-innerΜ Μ Ψ Ξ₁ D)

  sq-L-innerΦ : ∀ (Φ Μ Ψ Ξ₁ D : Ctx)
    → flattenˡ Φ Μ (Ψ ++ Ξ₁) D
      ∙ ((ap (λ l → Φ ++ Μ ++ l) (++-assoc Ψ Ξ₁ D)
          ∙ assocₘ-flatten Φ Μ Ψ (Ξ₁ ++ D))
         ∙ sym (++-assoc (Φ ++ Μ ++ Ψ) Ξ₁ D))
    ≡ ap (_++ D) (assocₘ-flatten Φ Μ Ψ Ξ₁)
  sq-L-innerΦ []      Μ Ψ Ξ₁ D = sq-L-innerΜ Μ Ψ Ξ₁ D
  sq-L-innerΦ (a ∷ Φ) Μ Ψ Ξ₁ D =
    sq-step a
      (flattenˡ Φ Μ (Ψ ++ Ξ₁) D)
      (ap (λ l → Φ ++ Μ ++ l) (++-assoc Ψ Ξ₁ D))
      (assocₘ-flatten Φ Μ Ψ (Ξ₁ ++ D))
      (sym (++-assoc (Φ ++ Μ ++ Ψ) Ξ₁ D))
      (sq-L-innerΦ Φ Μ Ψ Ξ₁ D)

  sq-L-inner : ∀ (Θ Φ Μ Ψ Ξ₁ D : Ctx)
    → flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) D
      ∙ ((ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ D)
          ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ D))
         ∙ sym (flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ D))
    ≡ ap (_++ D) (assocₘ-boundary Θ Φ Μ Ψ Ξ₁)
  sq-L-inner []      Φ Μ Ψ Ξ₁ D = sq-L-innerΦ Φ Μ Ψ Ξ₁ D
  sq-L-inner (a ∷ Θ) Φ Μ Ψ Ξ₁ D =
    sq-step a
      (flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) D)
      (ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ D))
      (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ D))
      (sym (flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ D))
      (sq-L-inner Θ Φ Μ Ψ Ξ₁ D)

  -- Inner square for the match⊗ on-right/on-right core: the binder segment
  -- against the boundary buried under Γm and the two bound slots.
  sq-B-inner⊗ : ∀ (Γm : Ctx) (a b : Ty) (Θ₃ Φ Μ Ψ Ξ : Ctx)
    → flattenʳ Γm (a ∷ b ∷ Θ₃ ++ Φ) Μ (Ψ ++ Ξ)
      ∙ ((ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (a ∷ b ∷ Θ₃) Φ))
          ∙ assocₘ-boundary (Γm ++ a ∷ b ∷ Θ₃) Φ Μ Ψ Ξ)
         ∙ sym (flattenʳ Γm (a ∷ b ∷ Θ₃) (Φ ++ Μ ++ Ψ) Ξ))
    ≡ ap (λ l → Γm ++ a ∷ b ∷ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ)
  sq-B-inner⊗ [] a b Θ₃ Φ Μ Ψ Ξ =
    sq-base (assocₘ-boundary (a ∷ b ∷ Θ₃) Φ Μ Ψ Ξ)
  sq-B-inner⊗ (a' ∷ Γm) a b Θ₃ Φ Μ Ψ Ξ =
    sq-step a'
      (flattenʳ Γm (a ∷ b ∷ Θ₃ ++ Φ) Μ (Ψ ++ Ξ))
      (ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (a ∷ b ∷ Θ₃) Φ)))
      (assocₘ-boundary (Γm ++ a ∷ b ∷ Θ₃) Φ Μ Ψ Ξ)
      (sym (flattenʳ Γm (a ∷ b ∷ Θ₃) (Φ ++ Μ ++ Ψ) Ξ))
      (sq-B-inner⊗ Γm a b Θ₃ Φ Μ Ψ Ξ)

  -- The 𝟙-variant: no bound slots.
  sq-B-inner𝟙 : ∀ (Γm Θ₃ Φ Μ Ψ Ξ : Ctx)
    → flattenʳ Γm (Θ₃ ++ Φ) Μ (Ψ ++ Ξ)
      ∙ ((ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ))
          ∙ assocₘ-boundary (Γm ++ Θ₃) Φ Μ Ψ Ξ)
         ∙ sym (flattenʳ Γm Θ₃ (Φ ++ Μ ++ Ψ) Ξ))
    ≡ ap (λ l → Γm ++ l) (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ)
  sq-B-inner𝟙 [] Θ₃ Φ Μ Ψ Ξ = sq-base (assocₘ-boundary Θ₃ Φ Μ Ψ Ξ)
  sq-B-inner𝟙 (a' ∷ Γm) Θ₃ Φ Μ Ψ Ξ =
    sq-step a'
      (flattenʳ Γm (Θ₃ ++ Φ) Μ (Ψ ++ Ξ))
      (ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ)))
      (assocₘ-boundary (Γm ++ Θ₃) Φ Μ Ψ Ξ)
      (sym (flattenʳ Γm Θ₃ (Φ ++ Μ ++ Ψ) Ξ))
      (sq-B-inner𝟙 Γm Θ₃ Φ Μ Ψ Ξ)

-- ==========================================================================
-- Canonicalisers.  Transport an associativity goal stated at the canonical
-- (weakened) split of a Split-++ case to the goal at the abstract split,
-- along the view's soundness field — everything applied under the interval
-- j.  Generic in the analysed term t (resp. spine ts), so all constructor
-- handlers share them.
-- ==========================================================================

canon-L
  : ∀ {x y z : Ty} {Θ Ξ Ξ₁ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (s₁ : Split x Θ Γ₁ Ξ₁) (p : Ξ₁ ++ Δ₁ ≡ Ξ)
    (co : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (p i)) (split-++ˡ s₁ Δ₁) s)
    (s' : Split y Φ Λ Ψ) (t : Tm (Γ₁ ++ Δ₁) z) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δ₁) i) z)
      (sub (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))) (sub (split-++ˡ s₁ Δ₁) t g) h)
      (sub (split-++ˡ s₁ Δ₁) t (sub s' g h))
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s t g) h)
      (sub s t (sub s' g h))
canon-L {z = z} {Θ = Θ} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₁ p co s' t g h core =
  transport
    (λ j → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (p j) i) z)
      (sub (split-++ʳ Θ (split-++ˡ s' (p j))) (sub (co j) t g) h)
      (sub (co j) t (sub s' g h)))
    core

canon-R
  : ∀ {x y z : Ty} {Θ Ξ Γ₁ Δ₁ Θ₂ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    (co : PathP (λ i → Split x (q i) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₂) s)
    (s' : Split y Φ Λ Ψ) (t : Tm (Γ₁ ++ Δ₁) z) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γ₁ ++ Θ₂) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)) (sub (split-++ʳ Γ₁ s₂) t g) h)
      (sub (split-++ʳ Γ₁ s₂) t (sub s' g h))
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s t g) h)
      (sub s t (sub s' g h))
canon-R {z = z} {Ξ = Ξ} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₂ q co s' t g h core =
  transport
    (λ j → PathP (λ i → Tm (assocₘ-boundary (q j) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (q j) (split-++ˡ s' Ξ)) (sub (co j) t g) h)
      (sub (co j) t (sub s' g h)))
    core

canon-L-sp
  : ∀ {x y : Ty} {As' : List (Multigraph.Ob G)}
    {Θ Ξ Ξ₁ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (s₁ : Split x Θ Γ₁ Ξ₁) (p : Ξ₁ ++ Δ₁ ≡ Ξ)
    (co : PathP (λ i → Split x Θ (Γ₁ ++ Δ₁) (p i)) (split-++ˡ s₁ Δ₁) s)
    (s' : Split y Φ Λ Ψ) (ts : Sp (Γ₁ ++ Δ₁) As') (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δ₁) i) As')
      (sub-sp (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))) (sub-sp (split-++ˡ s₁ Δ₁) ts g) h)
      (sub-sp (split-++ˡ s₁ Δ₁) ts (sub s' g h))
  → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ Ξ i) As')
      (sub-sp (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub-sp s ts g) h)
      (sub-sp s ts (sub s' g h))
canon-L-sp {As' = As'} {Θ = Θ} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₁ p co s' ts g h core =
  transport
    (λ j → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ (p j) i) As')
      (sub-sp (split-++ʳ Θ (split-++ˡ s' (p j))) (sub-sp (co j) ts g) h)
      (sub-sp (co j) ts (sub s' g h)))
    core

canon-R-sp
  : ∀ {x y : Ty} {As' : List (Multigraph.Ob G)}
    {Θ Ξ Γ₁ Δ₁ Θ₂ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    (co : PathP (λ i → Split x (q i) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₂) s)
    (s' : Split y Φ Λ Ψ) (ts : Sp (Γ₁ ++ Δ₁) As') (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Sp (assocₘ-boundary (Γ₁ ++ Θ₂) Φ Μ Ψ Ξ i) As')
      (sub-sp (split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)) (sub-sp (split-++ʳ Γ₁ s₂) ts g) h)
      (sub-sp (split-++ʳ Γ₁ s₂) ts (sub s' g h))
  → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ Ξ i) As')
      (sub-sp (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub-sp s ts g) h)
      (sub-sp s ts (sub s' g h))
canon-R-sp {As' = As'} {Ξ = Ξ} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₂ q co s' ts g h core =
  transport
    (λ j → PathP (λ i → Sp (assocₘ-boundary (q j) Φ Μ Ψ Ξ i) As')
      (sub-sp (split-++ʳ (q j) (split-++ˡ s' Ξ)) (sub-sp (co j) ts g) h)
      (sub-sp (co j) ts (sub s' g h)))
    core

-- Second-stage canonicalisers, for the match ʳ-handlers: the analysed split
-- sits under a prefix burial split-++ʳ Γm.
canon-Lᵐ
  : ∀ {x y z : Ty} {Γm Θ₂ Ξ Ξ₁ Ψm Δm Φ Λ Ψ Μ : Ctx} {s'' : Split x Θ₂ (Ψm ++ Δm) Ξ}
    (s₁ : Split x Θ₂ Ψm Ξ₁) (p : Ξ₁ ++ Δm ≡ Ξ)
    (co : PathP (λ i → Split x Θ₂ (Ψm ++ Δm) (p i)) (split-++ˡ s₁ Δm) s'')
    (s' : Split y Φ Λ Ψ) (t : Tm (Γm ++ Ψm ++ Δm) z) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ (Ξ₁ ++ Δm) i) z)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm)))
           (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) t g) h)
      (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) t (sub s' g h))
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' Ξ)) (sub (split-++ʳ Γm s'') t g) h)
      (sub (split-++ʳ Γm s'') t (sub s' g h))
canon-Lᵐ {z = z} {Γm = Γm} {Θ₂ = Θ₂} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₁ p co s' t g h core =
  transport
    (λ j → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ (p j) i) z)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (p j))) (sub (split-++ʳ Γm (co j)) t g) h)
      (sub (split-++ʳ Γm (co j)) t (sub s' g h)))
    core

canon-Rᵐ
  : ∀ {x y z : Ty} {Γm Θ₂ Ξ Θ₃ Ψm Δm Φ Λ Ψ Μ : Ctx} {s'' : Split x Θ₂ (Ψm ++ Δm) Ξ}
    (s₂ : Split x Θ₃ Δm Ξ) (q : Ψm ++ Θ₃ ≡ Θ₂)
    (co : PathP (λ i → Split x (q i) (Ψm ++ Δm) Ξ) (split-++ʳ Ψm s₂) s'')
    (s' : Split y Φ Λ Ψ) (t : Tm (Γm ++ Ψm ++ Δm) z) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Ψm ++ Θ₃) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ))
           (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) t g) h)
      (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) t (sub s' g h))
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' Ξ)) (sub (split-++ʳ Γm s'') t g) h)
      (sub (split-++ʳ Γm s'') t (sub s' g h))
canon-Rᵐ {z = z} {Γm = Γm} {Ξ = Ξ} {Φ = Φ} {Ψ = Ψ} {Μ = Μ} s₂ q co s' t g h core =
  transport
    (λ j → PathP (λ i → Tm (assocₘ-boundary (Γm ++ q j) Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ (Γm ++ q j) (split-++ˡ s' Ξ)) (sub (split-++ʳ Γm (co j)) t g) h)
      (sub (split-++ʳ Γm (co j)) t (sub s' g h)))
    core

-- ==========================================================================
-- The mutual induction.  The two top-level lemmas dispatch on the term
-- constructor and hand the view to a handler per constructor; each handler
-- canonicalises the split (canon-*) and invokes a core lemma in which the
-- split is a literal weakening, so both sides reduce through sub's handlers
-- by the split-++-ˡ/ʳ computation rules.
-- ==========================================================================

sub-assoc : ∀ {x y z Θ Ρ Ξ Φ Λ Ψ Μ}
            (s : Split x Θ Ρ Ξ) (s' : Split y Φ Λ Ψ)
            (t : Tm Ρ z) (g : Tm Λ x) (h : Tm Μ y)
          → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) z)
              (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s t g) h)
              (sub s t (sub s' g h))

sub-sp-assoc : ∀ {x y Θ Ρ Ξ Φ Λ Ψ Μ} {As : List (Multigraph.Ob G)}
               (s : Split x Θ Ρ Ξ) (s' : Split y Φ Λ Ψ)
               (ts : Sp Ρ As) (g : Tm Λ x) (h : Tm Μ y)
             → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ Ξ i) As)
                 (sub-sp (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub-sp s ts g) h)
                 (sub-sp s ts (sub s' g h))

-- ---- handlers (one per constructor, dispatching on the view) -------------

sub-assoc-var
  : ∀ {x y z : Ty} {Θ Ξ Φ Λ Ψ Μ : Ctx}
    (s : Split x Θ (z ∷ []) Ξ) (s' : Split y Φ Λ Ψ) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) z)
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub-var s g) h)
      (sub-var s (sub s' g h))

sub-assoc-pair
  : ∀ {x y A B : Ty} {Θ Ξ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
  → Split-++ Γ₁ Δ₁ s
  → (s' : Split y Φ Λ Ψ) (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) (A ⊗ B))
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s ⦅ P , Q ⦆ g) h)
      (sub s ⦅ P , Q ⦆ (sub s' g h))

sub-assoc-cons
  : ∀ {x y : Ty} {A : Multigraph.Ob G} {As : List (Multigraph.Ob G)}
    {Θ Ξ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
  → Split-++ Γ₁ Δ₁ s
  → (s' : Split y Φ Λ Ψ) (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As)
    (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ Ξ i) (A ∷ As))
      (sub-sp (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub-sp s (t ∷ ts) g) h)
      (sub-sp s (t ∷ ts) (sub s' g h))

sub-assoc-m⊗
  : ∀ {x y A B C : Ty} {Θ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
  → Split-++ Γm (Ψm ++ Δm) s
  → (s' : Split y Φ Λ Ψ) (P : Tm Ψm (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
    (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub s (match⊗ {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

sub-assoc-m⊗ʳ
  : ∀ {x y A B C : Ty} {Θ₂ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    {s'' : Split x Θ₂ (Ψm ++ Δm) Ξ}
  → Split-++ Ψm Δm s''
  → (s' : Split y Φ Λ Ψ) (P : Tm Ψm (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
    (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' Ξ))
           (sub (split-++ʳ Γm s'') (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm s'') (match⊗ {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

sub-assoc-m𝟙
  : ∀ {x y C : Ty} {Θ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    {s : Split x Θ (Γm ++ Ψm ++ Δm) Ξ}
  → Split-++ Γm (Ψm ++ Δm) s
  → (s' : Split y Φ Λ Ψ) (P : Tm Ψm 𝟙) (Q : Tm (Γm ++ Δm) C)
    (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ Θ (split-++ˡ s' Ξ)) (sub s (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub s (match𝟙 {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

sub-assoc-m𝟙ʳ
  : ∀ {x y C : Ty} {Θ₂ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    {s'' : Split x Θ₂ (Ψm ++ Δm) Ξ}
  → Split-++ Ψm Δm s''
  → (s' : Split y Φ Λ Ψ) (P : Tm Ψm 𝟙) (Q : Tm (Γm ++ Δm) C)
    (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' Ξ))
           (sub (split-++ʳ Γm s'') (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm s'') (match𝟙 {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

-- ---- cores (splits are literal weakenings; views compute) ----------------

core-pair-L
  : ∀ {x y A B : Ty} {Θ Ξ₁ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ Γ₁ Ξ₁) (s' : Split y Φ Λ Ψ)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δ₁) i) (A ⊗ B))
      (sub (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))) (sub (split-++ˡ s₁ Δ₁) ⦅ P , Q ⦆ g) h)
      (sub (split-++ˡ s₁ Δ₁) ⦅ P , Q ⦆ (sub s' g h))

core-pair-R
  : ∀ {x y A B : Ty} {Θ₂ Ξ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (s' : Split y Φ Λ Ψ)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γ₁ ++ Θ₂) Φ Μ Ψ Ξ i) (A ⊗ B))
      (sub (split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)) (sub (split-++ʳ Γ₁ s₂) ⦅ P , Q ⦆ g) h)
      (sub (split-++ʳ Γ₁ s₂) ⦅ P , Q ⦆ (sub s' g h))

core-cons-L
  : ∀ {x y : Ty} {A : Multigraph.Ob G} {As : List (Multigraph.Ob G)}
    {Θ Ξ₁ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ Γ₁ Ξ₁) (s' : Split y Φ Λ Ψ)
    (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Sp (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δ₁) i) (A ∷ As))
      (sub-sp (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))) (sub-sp (split-++ˡ s₁ Δ₁) (t ∷ ts) g) h)
      (sub-sp (split-++ˡ s₁ Δ₁) (t ∷ ts) (sub s' g h))

core-cons-R
  : ∀ {x y : Ty} {A : Multigraph.Ob G} {As : List (Multigraph.Ob G)}
    {Θ₂ Ξ Γ₁ Δ₁ Φ Λ Ψ Μ : Ctx}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (s' : Split y Φ Λ Ψ)
    (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Sp (assocₘ-boundary (Γ₁ ++ Θ₂) Φ Μ Ψ Ξ i) (A ∷ As))
      (sub-sp (split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)) (sub-sp (split-++ʳ Γ₁ s₂) (t ∷ ts) g) h)
      (sub-sp (split-++ʳ Γ₁ s₂) (t ∷ ts) (sub s' g h))

core-m⊗-L
  : ∀ {x y A B C : Ty} {Θ Ξ₁ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ Γm Ξ₁) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Ψm ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Ψm ++ Δm)))
           (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

core-m⊗-M
  : ∀ {x y A B C : Ty} {Θ₂ Ξ₁ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ₂ Ψm Ξ₁) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ (Ξ₁ ++ Δm) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm)))
           (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

core-m⊗-B
  : ∀ {x y A B C : Ty} {Θ₃ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₂ : Split x Θ₃ Δm Ξ) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Ψm ++ Θ₃) Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ))
           (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

core-m𝟙-L
  : ∀ {x y C : Ty} {Θ Ξ₁ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ Γm Ξ₁) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Ψm ++ Δm) i) C)
      (sub (split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Ψm ++ Δm)))
           (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

core-m𝟙-M
  : ∀ {x y C : Ty} {Θ₂ Ξ₁ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₁ : Split x Θ₂ Ψm Ξ₁) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Θ₂) Φ Μ Ψ (Ξ₁ ++ Δm) i) C)
      (sub (split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm)))
           (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

core-m𝟙-B
  : ∀ {x y C : Ty} {Θ₃ Ξ Γm Ψm Δm Φ Λ Ψ Μ : Ctx}
    (s₂ : Split x Θ₃ Δm Ξ) (s' : Split y Φ Λ Ψ)
    (P : Tm Ψm 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Λ x) (h : Tm Μ y)
  → PathP (λ i → Tm (assocₘ-boundary (Γm ++ Ψm ++ Θ₃) Φ Μ Ψ Ξ i) C)
      (sub (split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ))
           (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h)
      (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) (sub s' g h))

-- ---- dispatch ------------------------------------------------------------

sub-assoc s s' var            g h = sub-assoc-var s s' g h
sub-assoc s s' (gen f ts)     g h = λ i → gen f (sub-sp-assoc s s' ts g h i)
sub-assoc s s' (⦅_,_⦆ {Γ = Γ₁} P Q) g h = sub-assoc-pair (split-++ Γ₁ s) s' P Q g h
sub-assoc s s' (match⊗ {Γ = Γm} P Q) g h = sub-assoc-m⊗ (split-++ Γm s) s' P Q g h
sub-assoc s s' ⋆              g h = absurd (split-[] s)
sub-assoc s s' (match𝟙 {Γ = Γm} P Q) g h = sub-assoc-m𝟙 (split-++ Γm s) s' P Q g h

sub-sp-assoc s s' []                  g h = absurd (split-[] s)
sub-sp-assoc s s' (_∷_ {Γ = Γ₁} t ts) g h = sub-assoc-cons (split-++ Γ₁ s) s' t ts g h

-- ---- var -----------------------------------------------------------------

sub-assoc-var {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} here s' g h =
  tm-over (var-α Φ Μ Ψ)
    (tm-∙P {P = λ i → Φ ++ Μ ++ ++-idr Ψ i} {Q = sym (++-idr (Φ ++ Μ ++ Ψ))}
      (sub-pathp (split-++ˡ-idr s')
        (symP (cast-filler (sym (++-idr Λ)) g))
        (refl {x = h}))
      (cast-filler (sym (++-idr (Φ ++ Μ ++ Ψ))) (sub s' g h)))
sub-assoc-var (there s) s' g h = absurd (split-[] s)

-- ---- handler dispatch on the view ----------------------------------------

sub-assoc-pair (on-left s₁ p co) s' P Q g h =
  canon-L s₁ p co s' ⦅ P , Q ⦆ g h (core-pair-L s₁ s' P Q g h)
sub-assoc-pair (on-right s₂ q co) s' P Q g h =
  canon-R s₂ q co s' ⦅ P , Q ⦆ g h (core-pair-R s₂ s' P Q g h)

sub-assoc-cons (on-left s₁ p co) s' t ts g h =
  canon-L-sp s₁ p co s' (t ∷ ts) g h (core-cons-L s₁ s' t ts g h)
sub-assoc-cons (on-right s₂ q co) s' t ts g h =
  canon-R-sp s₂ q co s' (t ∷ ts) g h (core-cons-R s₂ s' t ts g h)

sub-assoc-m⊗ {Γm = Γm} {Δm = Δm} (on-left s₁ p co) s' P Q g h =
  canon-L s₁ p co s' (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h (core-m⊗-L {Γm = Γm} {Δm = Δm} s₁ s' P Q g h)
sub-assoc-m⊗ {Ψm = Ψm} {Δm = Δm} (on-right s'' q co) s' P Q g h =
  canon-R s'' q co s' (match⊗ {Δ = Δm} P Q) g h
    (sub-assoc-m⊗ʳ (split-++ Ψm s'') s' P Q g h)

sub-assoc-m⊗ʳ {Γm = Γm} {Δm = Δm} (on-left s₁ p co) s' P Q g h =
  canon-Lᵐ {Γm = Γm} s₁ p co s' (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h (core-m⊗-M {Γm = Γm} {Δm = Δm} s₁ s' P Q g h)
sub-assoc-m⊗ʳ {Γm = Γm} {Δm = Δm} (on-right s₂ q co) s' P Q g h =
  canon-Rᵐ {Γm = Γm} s₂ q co s' (match⊗ {Γ = Γm} {Δ = Δm} P Q) g h (core-m⊗-B {Γm = Γm} {Δm = Δm} s₂ s' P Q g h)

sub-assoc-m𝟙 {Γm = Γm} {Δm = Δm} (on-left s₁ p co) s' P Q g h =
  canon-L s₁ p co s' (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h (core-m𝟙-L {Γm = Γm} {Δm = Δm} s₁ s' P Q g h)
sub-assoc-m𝟙 {Ψm = Ψm} {Δm = Δm} (on-right s'' q co) s' P Q g h =
  canon-R s'' q co s' (match𝟙 {Δ = Δm} P Q) g h
    (sub-assoc-m𝟙ʳ (split-++ Ψm s'') s' P Q g h)

sub-assoc-m𝟙ʳ {Γm = Γm} {Δm = Δm} (on-left s₁ p co) s' P Q g h =
  canon-Lᵐ {Γm = Γm} s₁ p co s' (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h (core-m𝟙-M {Γm = Γm} {Δm = Δm} s₁ s' P Q g h)
sub-assoc-m𝟙ʳ {Γm = Γm} {Δm = Δm} (on-right s₂ q co) s' P Q g h =
  canon-Rᵐ {Γm = Γm} s₂ q co s' (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g h (core-m𝟙-B {Γm = Γm} {Δm = Δm} s₂ s' P Q g h)

-- ---- core bodies ---------------------------------------------------------

core-pair-L {x = x} {y = y} {A = A} {B = B} {Θ = Θ} {Ξ₁ = Ξ₁} {Γ₁ = Γ₁} {Δ₁ = Δ₁}
  {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' P Q g h =
  tm-over (sq-L Θ Φ Μ Ψ Ξ₁ Δ₁) (eL ◁ chain ▷ sym eR)
  where
    TmΩ : Ctx → Type _
    TmΩ Ω = Tm Ω (A ⊗ B)

    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₁ : (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bd₁ = assocₘ-boundary Θ Φ Μ Ψ Ξ₁

    flᴸ : (Θ ++ Λ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Λ ++ Ξ₁ ++ Δ₁
    flᴸ = flattenˡ Θ Λ Ξ₁ Δ₁

    flᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Δ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δ₁
    flᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁

    qᴸ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Δ₁ ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δ₁
    qᴸ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) Δ₁

    S : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ Δ₁) (Ψ ++ Ξ₁ ++ Δ₁)
    S = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))

    S₀ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    S₀ = split-++ʳ Θ (split-++ˡ s' Ξ₁)

    Sᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ Δ₁) ((Ψ ++ Ξ₁) ++ Δ₁)
    Sᶜ = split-++ˡ S₀ Δ₁

    W₁ : Tm (Θ ++ Λ ++ Ξ₁) A
    W₁ = sub s₁ P g

    W : TmΩ ((Θ ++ Λ ++ Ξ₁) ++ Δ₁)
    W = ⦅ W₁ , Q ⦆

    ihL : Tm ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) A
    ihL = sub S₀ W₁ h

    ih : PathP (λ i → Tm (bd₁ i) A) ihL (sub s₁ P gh)
    ih = sub-assoc s₁ s' P g h

    eL : sub S (sub (split-++ˡ s₁ Δ₁) ⦅ P , Q ⦆ g) h ≡ sub S (cast flᴸ W) h
    eL = ap (λ v → sub S (sub-pair v P Q g) h) (split-++-ˡ s₁ Δ₁)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → TmΩ ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ i))
          (sub Sᶜ W h) (sub S (cast flᴸ W) h)
    π i = sub (co-L Θ s' Ξ₁ Δ₁ i) (cast-filler flᴸ W i) h

    eC : sub Sᶜ W h ≡ cast qᴸ ⦅ ihL , Q ⦆
    eC = ap (λ v → sub-pair v W₁ Q h) (split-++-ˡ S₀ Δ₁)
       ∙ cast-∙idr qᴸ ⦅ ihL , Q ⦆

    eR : sub (split-++ˡ s₁ Δ₁) ⦅ P , Q ⦆ gh ≡ cast flᴱ ⦅ sub s₁ P gh , Q ⦆
    eR = ap (λ v → sub-pair v P Q gh) (split-++-ˡ s₁ Δ₁)
       ∙ cast-∙idr flᴱ ⦅ sub s₁ P gh , Q ⦆

    chain : PathP (λ i → TmΩ ((sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ j)
                    ∙ ((sym qᴸ ∙ ap (_++ Δ₁) bd₁) ∙ flᴱ)) i))
              (sub S (cast flᴸ W) h) (cast flᴱ ⦅ sub s₁ P gh , Q ⦆)
    chain =
      tm-∙P {P = sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ j)}
            {Q = (sym qᴸ ∙ ap (_++ Δ₁) bd₁) ∙ flᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᴸ ∙ ap (_++ Δ₁) bd₁} {Q = flᴱ}
          (tm-∙P {P = sym qᴸ} {Q = ap (_++ Δ₁) bd₁}
            (symP (cast-filler qᴸ ⦅ ihL , Q ⦆))
            (λ i → ⦅ ih i , Q ⦆))
          (cast-filler flᴱ ⦅ sub s₁ P gh , Q ⦆))
core-pair-R {x = x} {y = y} {A = A} {B = B} {Θ₂ = Θ₂} {Ξ = Ξ} {Γ₁ = Γ₁}
  {Δ₁ = Δ₁} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₂ s' P Q g h =
  tm-over (sq-R Γ₁ Θ₂ Φ Μ Ψ Ξ) (eL ◁ chain ▷ sym eR)
  where
    TmΩ : Ctx → Type _
    TmΩ Ω = Tm Ω (A ⊗ B)

    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₂ : (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bd₂ = assocₘ-boundary Θ₂ Φ Μ Ψ Ξ

    flᴸ : Γ₁ ++ Θ₂ ++ Λ ++ Ξ ≡ (Γ₁ ++ Θ₂) ++ Λ ++ Ξ
    flᴸ = flattenʳ Γ₁ Θ₂ Λ Ξ

    flᴱ : Γ₁ ++ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ ≡ (Γ₁ ++ Θ₂) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    flᴱ = flattenʳ Γ₁ Θ₂ (Φ ++ Μ ++ Ψ) Ξ

    qᴸ : Γ₁ ++ (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ (Γ₁ ++ Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qᴸ = flattenʳ Γ₁ (Θ₂ ++ Φ) Μ (Ψ ++ Ξ)

    S : Split y ((Γ₁ ++ Θ₂) ++ Φ) ((Γ₁ ++ Θ₂) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S = split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)

    S₂ᶜ : Split y (Θ₂ ++ Φ) (Θ₂ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S₂ᶜ = split-++ʳ Θ₂ (split-++ˡ s' Ξ)

    Sᶜ : Split y (Γ₁ ++ Θ₂ ++ Φ) (Γ₁ ++ Θ₂ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᶜ = split-++ʳ Γ₁ S₂ᶜ

    W₂ : Tm (Θ₂ ++ Λ ++ Ξ) B
    W₂ = sub s₂ Q g

    W : TmΩ (Γ₁ ++ Θ₂ ++ Λ ++ Ξ)
    W = ⦅ P , W₂ ⦆

    ihL : Tm ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ) B
    ihL = sub S₂ᶜ W₂ h

    ih : PathP (λ i → Tm (bd₂ i) B) ihL (sub s₂ Q gh)
    ih = sub-assoc s₂ s' Q g h

    eL : sub S (sub (split-++ʳ Γ₁ s₂) ⦅ P , Q ⦆ g) h ≡ sub S (cast flᴸ W) h
    eL = ap (λ v → sub S (sub-pair v P Q g) h) (split-++-ʳ Γ₁ s₂)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → TmΩ (sym (++-assoc Γ₁ Θ₂ Φ) i ++ Μ ++ Ψ ++ Ξ))
          (sub Sᶜ W h) (sub S (cast flᴸ W) h)
    π i = sub (co-R Γ₁ Θ₂ s' Ξ i) (cast-filler flᴸ W i) h

    eC : sub Sᶜ W h ≡ cast qᴸ ⦅ P , ihL ⦆
    eC = ap (λ v → sub-pair v P W₂ h) (split-++-ʳ Γ₁ S₂ᶜ)
       ∙ cast-∙idr qᴸ ⦅ P , ihL ⦆

    eR : sub (split-++ʳ Γ₁ s₂) ⦅ P , Q ⦆ gh ≡ cast flᴱ ⦅ P , sub s₂ Q gh ⦆
    eR = ap (λ v → sub-pair v P Q gh) (split-++-ʳ Γ₁ s₂)
       ∙ cast-∙idr flᴱ ⦅ P , sub s₂ Q gh ⦆

    chain : PathP (λ i → TmΩ ((sym (λ j → sym (++-assoc Γ₁ Θ₂ Φ) j ++ Μ ++ Ψ ++ Ξ)
                    ∙ ((sym qᴸ ∙ ap (Γ₁ ++_) bd₂) ∙ flᴱ)) i))
              (sub S (cast flᴸ W) h) (cast flᴱ ⦅ P , sub s₂ Q gh ⦆)
    chain =
      tm-∙P {P = sym (λ j → sym (++-assoc Γ₁ Θ₂ Φ) j ++ Μ ++ Ψ ++ Ξ)}
            {Q = (sym qᴸ ∙ ap (Γ₁ ++_) bd₂) ∙ flᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᴸ ∙ ap (Γ₁ ++_) bd₂} {Q = flᴱ}
          (tm-∙P {P = sym qᴸ} {Q = ap (Γ₁ ++_) bd₂}
            (symP (cast-filler qᴸ ⦅ P , ihL ⦆))
            (λ i → ⦅ P , ih i ⦆))
          (cast-filler flᴱ ⦅ P , sub s₂ Q gh ⦆))
core-cons-L {x = x} {y = y} {A = A} {As = As} {Θ = Θ} {Ξ₁ = Ξ₁} {Γ₁ = Γ₁}
  {Δ₁ = Δ₁} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' t ts g h =
  sp-over (sq-L Θ Φ Μ Ψ Ξ₁ Δ₁) (eL ◁ chain ▷ sym eR)
  where
    SpΩ : Ctx → Type _
    SpΩ Ω = Sp Ω (A ∷ As)

    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₁ : (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bd₁ = assocₘ-boundary Θ Φ Μ Ψ Ξ₁

    flᴸ : (Θ ++ Λ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Λ ++ Ξ₁ ++ Δ₁
    flᴸ = flattenˡ Θ Λ Ξ₁ Δ₁

    flᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Δ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δ₁
    flᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ Δ₁

    qᴸ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Δ₁ ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δ₁
    qᴸ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) Δ₁

    S : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ Δ₁) (Ψ ++ Ξ₁ ++ Δ₁)
    S = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δ₁))

    S₀ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    S₀ = split-++ʳ Θ (split-++ˡ s' Ξ₁)

    Sᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ Δ₁) ((Ψ ++ Ξ₁) ++ Δ₁)
    Sᶜ = split-++ˡ S₀ Δ₁

    W₁ : Tm (Θ ++ Λ ++ Ξ₁) (base A)
    W₁ = sub s₁ t g

    W : SpΩ ((Θ ++ Λ ++ Ξ₁) ++ Δ₁)
    W = W₁ ∷ ts

    ihL : Tm ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) (base A)
    ihL = sub S₀ W₁ h

    ih : PathP (λ i → Tm (bd₁ i) (base A)) ihL (sub s₁ t gh)
    ih = sub-assoc s₁ s' t g h

    eL : sub-sp S (sub-sp (split-++ˡ s₁ Δ₁) (t ∷ ts) g) h ≡ sub-sp S (sp-cast flᴸ W) h
    eL = ap (λ v → sub-sp S (sub-cons v t ts g) h) (split-++-ˡ s₁ Δ₁)
       ∙ ap (λ ρ → sub-sp S (sp-cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → SpΩ ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ i))
          (sub-sp Sᶜ W h) (sub-sp S (sp-cast flᴸ W) h)
    π i = sub-sp (co-L Θ s' Ξ₁ Δ₁ i) (sp-cast-filler flᴸ W i) h

    eC : sub-sp Sᶜ W h ≡ sp-cast qᴸ (ihL ∷ ts)
    eC = ap (λ v → sub-cons v W₁ ts h) (split-++-ˡ S₀ Δ₁)
       ∙ sp-cast-∙idr qᴸ (ihL ∷ ts)

    eR : sub-sp (split-++ˡ s₁ Δ₁) (t ∷ ts) gh ≡ sp-cast flᴱ (sub s₁ t gh ∷ ts)
    eR = ap (λ v → sub-cons v t ts gh) (split-++-ˡ s₁ Δ₁)
       ∙ sp-cast-∙idr flᴱ (sub s₁ t gh ∷ ts)

    chain : PathP (λ i → SpΩ ((sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ j)
                    ∙ ((sym qᴸ ∙ ap (_++ Δ₁) bd₁) ∙ flᴱ)) i))
              (sub-sp S (sp-cast flᴸ W) h) (sp-cast flᴱ (sub s₁ t gh ∷ ts))
    chain =
      sp-∙P {P = sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δ₁ j)}
            {Q = (sym qᴸ ∙ ap (_++ Δ₁) bd₁) ∙ flᴱ}
        (symP π ▷ eC)
        (sp-∙P {P = sym qᴸ ∙ ap (_++ Δ₁) bd₁} {Q = flᴱ}
          (sp-∙P {P = sym qᴸ} {Q = ap (_++ Δ₁) bd₁}
            (symP (sp-cast-filler qᴸ (ihL ∷ ts)))
            (λ i → ih i ∷ ts))
          (sp-cast-filler flᴱ (sub s₁ t gh ∷ ts)))
core-cons-R {x = x} {y = y} {A = A} {As = As} {Θ₂ = Θ₂} {Ξ = Ξ} {Γ₁ = Γ₁}
  {Δ₁ = Δ₁} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₂ s' t ts g h =
  sp-over (sq-R Γ₁ Θ₂ Φ Μ Ψ Ξ) (eL ◁ chain ▷ sym eR)
  where
    SpΩ : Ctx → Type _
    SpΩ Ω = Sp Ω (A ∷ As)

    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₂ : (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bd₂ = assocₘ-boundary Θ₂ Φ Μ Ψ Ξ

    flᴸ : Γ₁ ++ Θ₂ ++ Λ ++ Ξ ≡ (Γ₁ ++ Θ₂) ++ Λ ++ Ξ
    flᴸ = flattenʳ Γ₁ Θ₂ Λ Ξ

    flᴱ : Γ₁ ++ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ ≡ (Γ₁ ++ Θ₂) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    flᴱ = flattenʳ Γ₁ Θ₂ (Φ ++ Μ ++ Ψ) Ξ

    qᴸ : Γ₁ ++ (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ (Γ₁ ++ Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qᴸ = flattenʳ Γ₁ (Θ₂ ++ Φ) Μ (Ψ ++ Ξ)

    S : Split y ((Γ₁ ++ Θ₂) ++ Φ) ((Γ₁ ++ Θ₂) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S = split-++ʳ (Γ₁ ++ Θ₂) (split-++ˡ s' Ξ)

    S₂ᶜ : Split y (Θ₂ ++ Φ) (Θ₂ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S₂ᶜ = split-++ʳ Θ₂ (split-++ˡ s' Ξ)

    Sᶜ : Split y (Γ₁ ++ Θ₂ ++ Φ) (Γ₁ ++ Θ₂ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᶜ = split-++ʳ Γ₁ S₂ᶜ

    W₂ : Sp (Θ₂ ++ Λ ++ Ξ) As
    W₂ = sub-sp s₂ ts g

    W : SpΩ (Γ₁ ++ Θ₂ ++ Λ ++ Ξ)
    W = t ∷ W₂

    ihL : Sp ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ) As
    ihL = sub-sp S₂ᶜ W₂ h

    ih : PathP (λ i → Sp (bd₂ i) As) ihL (sub-sp s₂ ts gh)
    ih = sub-sp-assoc s₂ s' ts g h

    eL : sub-sp S (sub-sp (split-++ʳ Γ₁ s₂) (t ∷ ts) g) h ≡ sub-sp S (sp-cast flᴸ W) h
    eL = ap (λ v → sub-sp S (sub-cons v t ts g) h) (split-++-ʳ Γ₁ s₂)
       ∙ ap (λ ρ → sub-sp S (sp-cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → SpΩ (sym (++-assoc Γ₁ Θ₂ Φ) i ++ Μ ++ Ψ ++ Ξ))
          (sub-sp Sᶜ W h) (sub-sp S (sp-cast flᴸ W) h)
    π i = sub-sp (co-R Γ₁ Θ₂ s' Ξ i) (sp-cast-filler flᴸ W i) h

    eC : sub-sp Sᶜ W h ≡ sp-cast qᴸ (t ∷ ihL)
    eC = ap (λ v → sub-cons v t W₂ h) (split-++-ʳ Γ₁ S₂ᶜ)
       ∙ sp-cast-∙idr qᴸ (t ∷ ihL)

    eR : sub-sp (split-++ʳ Γ₁ s₂) (t ∷ ts) gh ≡ sp-cast flᴱ (t ∷ sub-sp s₂ ts gh)
    eR = ap (λ v → sub-cons v t ts gh) (split-++-ʳ Γ₁ s₂)
       ∙ sp-cast-∙idr flᴱ (t ∷ sub-sp s₂ ts gh)

    chain : PathP (λ i → SpΩ ((sym (λ j → sym (++-assoc Γ₁ Θ₂ Φ) j ++ Μ ++ Ψ ++ Ξ)
                    ∙ ((sym qᴸ ∙ ap (Γ₁ ++_) bd₂) ∙ flᴱ)) i))
              (sub-sp S (sp-cast flᴸ W) h) (sp-cast flᴱ (t ∷ sub-sp s₂ ts gh))
    chain =
      sp-∙P {P = sym (λ j → sym (++-assoc Γ₁ Θ₂ Φ) j ++ Μ ++ Ψ ++ Ξ)}
            {Q = (sym qᴸ ∙ ap (Γ₁ ++_) bd₂) ∙ flᴱ}
        (symP π ▷ eC)
        (sp-∙P {P = sym qᴸ ∙ ap (Γ₁ ++_) bd₂} {Q = flᴱ}
          (sp-∙P {P = sym qᴸ} {Q = ap (Γ₁ ++_) bd₂}
            (symP (sp-cast-filler qᴸ (t ∷ ihL)))
            (λ i → t ∷ ih i))
          (sp-cast-filler flᴱ (t ∷ sub-sp s₂ ts gh)))
core-m⊗-L {x = x} {y = y} {A = A} {B = B} {C = C} {Θ = Θ} {Ξ₁ = Ξ₁} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' P Q g h =
  tm-over (sq-L Θ Φ Μ Ψ Ξ₁ (Ψm ++ Δm)) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₁ : (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bd₁ = assocₘ-boundary Θ Φ Μ Ψ Ξ₁

    flᴸ : (Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm ≡ Θ ++ Λ ++ Ξ₁ ++ Ψm ++ Δm
    flᴸ = flattenˡ Θ Λ Ξ₁ (Ψm ++ Δm)

    flᴮ : (Θ ++ Λ ++ Ξ₁) ++ A ∷ B ∷ Δm ≡ Θ ++ Λ ++ Ξ₁ ++ A ∷ B ∷ Δm
    flᴮ = flattenˡ Θ Λ Ξ₁ (A ∷ B ∷ Δm)

    flᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Ψm ++ Δm
        ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Ψm ++ Δm
    flᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ (Ψm ++ Δm)

    flᴮᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ A ∷ B ∷ Δm
         ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ A ∷ B ∷ Δm
    flᴮᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ (A ∷ B ∷ Δm)

    qᴸ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Ψm ++ Δm
       ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Ψm ++ Δm
    qᴸ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) (Ψm ++ Δm)

    qᴮ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ A ∷ B ∷ Δm
       ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ A ∷ B ∷ Δm
    qᴮ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) (A ∷ B ∷ Δm)

    S : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ Ψm ++ Δm) (Ψ ++ Ξ₁ ++ Ψm ++ Δm)
    S = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Ψm ++ Δm))

    S₀ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    S₀ = split-++ʳ Θ (split-++ˡ s' Ξ₁)

    Sᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm) ((Ψ ++ Ξ₁) ++ Ψm ++ Δm)
    Sᶜ = split-++ˡ S₀ (Ψm ++ Δm)

    Sᴮ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ A ∷ B ∷ Δm) (Ψ ++ Ξ₁ ++ A ∷ B ∷ Δm)
    Sᴮ = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ A ∷ B ∷ Δm))

    Sᴮᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ A ∷ B ∷ Δm) ((Ψ ++ Ξ₁) ++ A ∷ B ∷ Δm)
    Sᴮᶜ = split-++ˡ S₀ (A ∷ B ∷ Δm)

    Wq : Tm (Θ ++ Λ ++ Ξ₁ ++ A ∷ B ∷ Δm) C
    Wq = sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g

    W' : Tm ((Θ ++ Λ ++ Ξ₁) ++ A ∷ B ∷ Δm) C
    W' = cast (sym flᴮ) Wq

    W : Tm ((Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm) C
    W = match⊗ {Γ = Θ ++ Λ ++ Ξ₁} {Δ = Δm} P W'

    X : Tm ((Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ A ∷ B ∷ Δm) C
    X = sub Sᴮᶜ W' h

    Qgh : Tm (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ A ∷ B ∷ Δm) C
    Qgh = sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q gh

    ihQ : PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ A ∷ B ∷ Δm) i) C)
            (sub Sᴮ Wq h) Qgh
    ihQ = sub-assoc (split-++ˡ s₁ (A ∷ B ∷ Δm)) s' Q g h

    eL : sub S (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᴸ W) h
    eL = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ˡ s₁ (Ψm ++ Δm))
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → Tm ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) i) C)
          (sub Sᶜ W h) (sub S (cast flᴸ W) h)
    π i = sub (co-L Θ s' Ξ₁ (Ψm ++ Δm) i) (cast-filler flᴸ W i) h

    eC : sub Sᶜ W h
       ≡ cast qᴸ (match⊗ {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))
    eC = ap (λ v → sub-match⊗ˡ v P W' h) (split-++-ˡ S₀ (Ψm ++ Δm))
       ∙ cast-∙idr qᴸ (match⊗ {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))

    eR : sub (split-++ˡ s₁ (Ψm ++ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast flᴱ (match⊗ {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))
    eR = ap (λ v → sub-match⊗ˡ v P Q gh) (split-++-ˡ s₁ (Ψm ++ Δm))
       ∙ cast-∙idr flᴱ (match⊗ {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))

    innerP : PathP (λ i → Tm ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (A ∷ B ∷ Δm) (~ i)) C)
               (sub Sᴮ Wq h) X
    innerP i = sub (co-L Θ s' Ξ₁ (A ∷ B ∷ Δm) (~ i)) (cast-filler (sym flᴮ) Wq i) h

    inner : PathP (λ i → Tm ((qᴮ ∙ ((ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ (A ∷ B ∷ Δm))
                    ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ A ∷ B ∷ Δm)) ∙ sym flᴮᴱ)) i) C)
              (cast (sym qᴮ) X) (cast (sym flᴮᴱ) Qgh)
    inner =
      tm-∙P {P = qᴮ}
            {Q = (ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ (A ∷ B ∷ Δm))
                  ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ A ∷ B ∷ Δm)) ∙ sym flᴮᴱ}
        (symP (cast-filler (sym qᴮ) X))
        (tm-∙P {P = ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ (A ∷ B ∷ Δm))
                    ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ A ∷ B ∷ Δm)}
               {Q = sym flᴮᴱ}
          (tm-∙P {P = ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ (A ∷ B ∷ Δm))}
                 {Q = assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ A ∷ B ∷ Δm)}
            (symP innerP) ihQ)
          (cast-filler (sym flᴮᴱ) Qgh))

    inner' : PathP (λ i → Tm (bd₁ i ++ A ∷ B ∷ Δm) C)
               (cast (sym qᴮ) X) (cast (sym flᴮᴱ) Qgh)
    inner' = tm-over (sq-L-inner Θ Φ Μ Ψ Ξ₁ (A ∷ B ∷ Δm)) inner

    mid : PathP (λ i → Tm (bd₁ i ++ Ψm ++ Δm) C)
            (match⊗ {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))
            (match⊗ {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))
    mid i = match⊗ {Γ = bd₁ i} {Δ = Δm} P (inner' i)

    chain : PathP (λ i → Tm ((sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) j)
                    ∙ ((sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁) ∙ flᴱ)) i) C)
              (sub S (cast flᴸ W) h)
              (cast flᴱ (match⊗ {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh)))
    chain =
      tm-∙P {P = sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) j)}
            {Q = (sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁) ∙ flᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁} {Q = flᴱ}
          (tm-∙P {P = sym qᴸ} {Q = ap (_++ Ψm ++ Δm) bd₁}
            (symP (cast-filler qᴸ (match⊗ {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))))
            mid)
          (cast-filler flᴱ (match⊗ {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))))
core-m⊗-M {x = x} {y = y} {A = A} {B = B} {C = C} {Θ₂ = Θ₂} {Ξ₁ = Ξ₁} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' P Q g h =
  tm-over (sq-M Γm Θ₂ Φ Μ Ψ Ξ₁ Δm) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bdᵖ : (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bdᵖ = assocₘ-boundary Θ₂ Φ Μ Ψ Ξ₁

    flᵐ : Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm ≡ (Γm ++ Θ₂) ++ Λ ++ Ξ₁ ++ Δm
    flᵐ = flattenᵐ Γm Θ₂ Λ Ξ₁ Δm

    flᵐᴱ : Γm ++ (Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Δm
         ≡ (Γm ++ Θ₂) ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δm
    flᵐᴱ = flattenᵐ Γm Θ₂ (Φ ++ Μ ++ Ψ) Ξ₁ Δm

    qᵐ : Γm ++ ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Δm
       ≡ (Γm ++ Θ₂ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δm
    qᵐ = flattenᵐ Γm (Θ₂ ++ Φ) Μ (Ψ ++ Ξ₁) Δm

    S : Split y ((Γm ++ Θ₂) ++ Φ) ((Γm ++ Θ₂) ++ Λ ++ Ξ₁ ++ Δm) (Ψ ++ Ξ₁ ++ Δm)
    S = split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm))

    Sᵢ : Split y (Θ₂ ++ Φ) (Θ₂ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    Sᵢ = split-++ʳ Θ₂ (split-++ˡ s' Ξ₁)

    Sᵢᶜ : Split y (Θ₂ ++ Φ) ((Θ₂ ++ Λ ++ Ξ₁) ++ Δm) ((Ψ ++ Ξ₁) ++ Δm)
    Sᵢᶜ = split-++ˡ Sᵢ Δm

    Sᶜ : Split y (Γm ++ Θ₂ ++ Φ) (Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm) ((Ψ ++ Ξ₁) ++ Δm)
    Sᶜ = split-++ʳ Γm Sᵢᶜ

    W₁ : Tm (Θ₂ ++ Λ ++ Ξ₁) (A ⊗ B)
    W₁ = sub s₁ P g

    W : Tm (Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm) C
    W = match⊗ {Γ = Γm} {Δ = Δm} W₁ Q

    ihL : Tm ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) (A ⊗ B)
    ihL = sub Sᵢ W₁ h

    ih : PathP (λ i → Tm (bdᵖ i) (A ⊗ B)) ihL (sub s₁ P gh)
    ih = sub-assoc s₁ s' P g h

    eL : sub S (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᵐ W) h
    eL = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁ Δm))
       ∙ ap (λ v → sub S (sub-match⊗ʳ v refl P Q g) h) (split-++-ˡ s₁ Δm)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᵐ)

    π : PathP (λ i → Tm (sym (++-assoc Γm Θ₂ Φ) i ++ Μ ++ ++-assoc Ψ Ξ₁ Δm i) C)
          (sub Sᶜ W h) (sub S (cast flᵐ W) h)
    π i = sub (co-M Γm Θ₂ s' Ξ₁ Δm i) (cast-filler flᵐ W i) h

    eC : sub Sᶜ W h ≡ cast qᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)
    eC = ap (λ v → sub-match⊗ˡ v W₁ Q h) (split-++-ʳ Γm Sᵢᶜ)
       ∙ ap (λ v → sub-match⊗ʳ v refl W₁ Q h) (split-++-ˡ Sᵢ Δm)
       ∙ cast-∙idr qᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)

    eR : sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast flᵐᴱ (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)
    eR = ap (λ v → sub-match⊗ˡ v P Q gh) (split-++-ʳ Γm (split-++ˡ s₁ Δm))
       ∙ ap (λ v → sub-match⊗ʳ v refl P Q gh) (split-++-ˡ s₁ Δm)
       ∙ cast-∙idr flᵐᴱ (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)

    mid : PathP (λ i → Tm (Γm ++ bdᵖ i ++ Δm) C)
            (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)
            (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)
    mid i = match⊗ {Γ = Γm} {Δ = Δm} (ih i) Q

    chain : PathP (λ i → Tm ((sym (λ j → sym (++-assoc Γm Θ₂ Φ) j ++ Μ ++ ++-assoc Ψ Ξ₁ Δm j)
                    ∙ ((sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ) ∙ flᵐᴱ)) i) C)
              (sub S (cast flᵐ W) h)
              (cast flᵐᴱ (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q))
    chain =
      tm-∙P {P = sym (λ j → sym (++-assoc Γm Θ₂ Φ) j ++ Μ ++ ++-assoc Ψ Ξ₁ Δm j)}
            {Q = (sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ) ∙ flᵐᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ} {Q = flᵐᴱ}
          (tm-∙P {P = sym qᵐ} {Q = ap (λ l → Γm ++ l ++ Δm) bdᵖ}
            (symP (cast-filler qᵐ (match⊗ {Γ = Γm} {Δ = Δm} ihL Q)))
            mid)
          (cast-filler flᵐᴱ (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)))
core-m⊗-B {x = x} {y = y} {A = A} {B = B} {C = C} {Θ₃ = Θ₃} {Ξ = Ξ} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₂ s' P Q g h =
  tm-over (sq-B Γm Ψm Θ₃ Φ Μ Ψ Ξ) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₃ : (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bd₃ = assocₘ-boundary Θ₃ Φ Μ Ψ Ξ

    bdᴮ : ((Γm ++ A ∷ B ∷ Θ₃) ++ Φ) ++ Μ ++ Ψ ++ Ξ
        ≡ (Γm ++ A ∷ B ∷ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bdᴮ = assocₘ-boundary (Γm ++ A ∷ B ∷ Θ₃) Φ Μ Ψ Ξ

    bu : Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ ≡ (Γm ++ Ψm ++ Θ₃) ++ Λ ++ Ξ
    bu = bury Γm Ψm Θ₃ (Λ ++ Ξ)

    buᴱ : Γm ++ Ψm ++ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
        ≡ (Γm ++ Ψm ++ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    buᴱ = bury Γm Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ)

    qᵇ : Γm ++ Ψm ++ (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
       ≡ (Γm ++ Ψm ++ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qᵇ = bury Γm Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ)

    flʳᴮ : Γm ++ (A ∷ B ∷ Θ₃) ++ Λ ++ Ξ ≡ (Γm ++ A ∷ B ∷ Θ₃) ++ Λ ++ Ξ
    flʳᴮ = flattenʳ Γm (A ∷ B ∷ Θ₃) Λ Ξ

    flʳᴮᴱ : Γm ++ (A ∷ B ∷ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
          ≡ (Γm ++ A ∷ B ∷ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    flʳᴮᴱ = flattenʳ Γm (A ∷ B ∷ Θ₃) (Φ ++ Μ ++ Ψ) Ξ

    qʳᴮ : Γm ++ (A ∷ B ∷ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
        ≡ (Γm ++ A ∷ B ∷ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qʳᴮ = flattenʳ Γm (A ∷ B ∷ Θ₃ ++ Φ) Μ (Ψ ++ Ξ)

    S : Split y ((Γm ++ Ψm ++ Θ₃) ++ Φ) ((Γm ++ Ψm ++ Θ₃) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S = split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ)

    Sᵣ' : Split y (Θ₃ ++ Φ) (Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᵣ' = split-++ʳ Θ₃ (split-++ˡ s' Ξ)

    Sᵣ : Split y (Ψm ++ Θ₃ ++ Φ) (Ψm ++ Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᵣ = split-++ʳ Ψm Sᵣ'

    Sᶜ : Split y (Γm ++ Ψm ++ Θ₃ ++ Φ) (Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᶜ = split-++ʳ Γm Sᵣ

    Sᴮ : Split y ((Γm ++ A ∷ B ∷ Θ₃) ++ Φ) ((Γm ++ A ∷ B ∷ Θ₃) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᴮ = split-++ʳ (Γm ++ A ∷ B ∷ Θ₃) (split-++ˡ s' Ξ)

    sq : Split x (Γm ++ A ∷ B ∷ Θ₃) (Γm ++ A ∷ B ∷ Δm) Ξ
    sq = split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)

    Wq : Tm ((Γm ++ A ∷ B ∷ Θ₃) ++ Λ ++ Ξ) C
    Wq = sub sq Q g

    W' : Tm (Γm ++ A ∷ B ∷ Θ₃ ++ Λ ++ Ξ) C
    W' = cast (sym flʳᴮ) Wq

    W : Tm (Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ) C
    W = match⊗ {Γ = Γm} {Δ = Θ₃ ++ Λ ++ Ξ} P W'

    X : Tm ((Γm ++ A ∷ B ∷ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ) C
    X = sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) Sᵣ')) W' h

    Qgh : Tm ((Γm ++ A ∷ B ∷ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ) C
    Qgh = sub sq Q gh

    Wq' : Tm (Γm ++ Ψm ++ (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ) C
    Wq' = match⊗ {Γ = Γm} {Δ = (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ} P (cast (sym qʳᴮ) X)

    Wᴱ : Tm (Γm ++ Ψm ++ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ) C
    Wᴱ = match⊗ {Γ = Γm} {Δ = Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ} P (cast (sym flʳᴮᴱ) Qgh)

    ihQ : PathP (λ i → Tm (bdᴮ i) C) (sub Sᴮ Wq h) Qgh
    ihQ = sub-assoc sq s' Q g h

    eL : sub S (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast bu W) h
    eL = ap (λ v → sub S (sub-match⊗ˡ v P Q g) h) (split-++-ʳ Γm (split-++ʳ Ψm s₂))
       ∙ ap (λ v → sub S (sub-match⊗ʳ v refl P Q g) h) (split-++-ʳ Ψm s₂)
       ∙ ap (λ w → sub S (cast (bu ∙ ap (_++ Λ ++ Ξ) w) W) h)
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃}))
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr bu)

    π : PathP (λ i → Tm (bury Γm Ψm Θ₃ Φ i ++ Μ ++ Ψ ++ Ξ) C)
          (sub Sᶜ W h) (sub S (cast bu W) h)
    π i = sub (co-B Γm Ψm Θ₃ s' Ξ i) (cast-filler bu W i) h

    eC : sub Sᶜ W h ≡ cast qᵇ Wq'
    eC = ap (λ v → sub-match⊗ˡ v P W' h) (split-++-ʳ Γm Sᵣ)
       ∙ ap (λ v → sub-match⊗ʳ v refl P W' h) (split-++-ʳ Ψm Sᵣ')
       ∙ ap (λ w → cast (qᵇ ∙ ap (_++ Μ ++ Ψ ++ Ξ) w) Wq')
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃ ++ Φ}))
       ∙ cast-∙idr qᵇ Wq'

    eR : sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match⊗ {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast buᴱ Wᴱ
    eR = ap (λ v → sub-match⊗ˡ v P Q gh) (split-++-ʳ Γm (split-++ʳ Ψm s₂))
       ∙ ap (λ v → sub-match⊗ʳ v refl P Q gh) (split-++-ʳ Ψm s₂)
       ∙ ap (λ w → cast (buᴱ ∙ ap (_++ (Φ ++ Μ ++ Ψ) ++ Ξ) w) Wᴱ)
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃}))
       ∙ cast-∙idr buᴱ Wᴱ

    innerP : PathP (λ i → Tm (++-assoc Γm (A ∷ B ∷ Θ₃) Φ i ++ Μ ++ Ψ ++ Ξ) C)
               (sub Sᴮ Wq h) X
    innerP i = sub (co-R Γm (A ∷ B ∷ Θ₃) s' Ξ (~ i)) (cast-filler (sym flʳᴮ) Wq i) h

    inner : PathP (λ i → Tm ((qʳᴮ ∙ ((ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (A ∷ B ∷ Θ₃) Φ))
                    ∙ bdᴮ) ∙ sym flʳᴮᴱ)) i) C)
              (cast (sym qʳᴮ) X) (cast (sym flʳᴮᴱ) Qgh)
    inner =
      tm-∙P {P = qʳᴮ}
            {Q = (ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (A ∷ B ∷ Θ₃) Φ)) ∙ bdᴮ)
                 ∙ sym flʳᴮᴱ}
        (symP (cast-filler (sym qʳᴮ) X))
        (tm-∙P {P = ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (A ∷ B ∷ Θ₃) Φ)) ∙ bdᴮ}
               {Q = sym flʳᴮᴱ}
          (tm-∙P {P = ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm (A ∷ B ∷ Θ₃) Φ))}
                 {Q = bdᴮ}
            (symP innerP) ihQ)
          (cast-filler (sym flʳᴮᴱ) Qgh))

    inner' : PathP (λ i → Tm (Γm ++ A ∷ B ∷ bd₃ i) C)
               (cast (sym qʳᴮ) X) (cast (sym flʳᴮᴱ) Qgh)
    inner' = tm-over (sq-B-inner⊗ Γm A B Θ₃ Φ Μ Ψ Ξ) inner

    mid : PathP (λ i → Tm (Γm ++ Ψm ++ bd₃ i) C) Wq' Wᴱ
    mid i = match⊗ {Γ = Γm} {Δ = bd₃ i} P (inner' i)

    chain : PathP (λ i → Tm ((sym (λ j → bury Γm Ψm Θ₃ Φ j ++ Μ ++ Ψ ++ Ξ)
                    ∙ ((sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃) ∙ buᴱ)) i) C)
              (sub S (cast bu W) h) (cast buᴱ Wᴱ)
    chain =
      tm-∙P {P = sym (λ j → bury Γm Ψm Θ₃ Φ j ++ Μ ++ Ψ ++ Ξ)}
            {Q = (sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃) ∙ buᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃} {Q = buᴱ}
          (tm-∙P {P = sym qᵇ} {Q = ap (λ l → Γm ++ Ψm ++ l) bd₃}
            (symP (cast-filler qᵇ Wq'))
            mid)
          (cast-filler buᴱ Wᴱ))
core-m𝟙-L {x = x} {y = y} {C = C} {Θ = Θ} {Ξ₁ = Ξ₁} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' P Q g h =
  tm-over (sq-L Θ Φ Μ Ψ Ξ₁ (Ψm ++ Δm)) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₁ : (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bd₁ = assocₘ-boundary Θ Φ Μ Ψ Ξ₁

    flᴸ : (Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm ≡ Θ ++ Λ ++ Ξ₁ ++ Ψm ++ Δm
    flᴸ = flattenˡ Θ Λ Ξ₁ (Ψm ++ Δm)

    flᴮ : (Θ ++ Λ ++ Ξ₁) ++ Δm ≡ Θ ++ Λ ++ Ξ₁ ++ Δm
    flᴮ = flattenˡ Θ Λ Ξ₁ Δm

    flᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Ψm ++ Δm
        ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Ψm ++ Δm
    flᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ (Ψm ++ Δm)

    flᴮᴱ : (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Δm
         ≡ Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δm
    flᴮᴱ = flattenˡ Θ (Φ ++ Μ ++ Ψ) Ξ₁ Δm

    qᴸ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Ψm ++ Δm
       ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Ψm ++ Δm
    qᴸ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) (Ψm ++ Δm)

    qᴮ : ((Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Δm
       ≡ (Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δm
    qᴮ = flattenˡ (Θ ++ Φ) Μ (Ψ ++ Ξ₁) Δm

    S : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ Ψm ++ Δm) (Ψ ++ Ξ₁ ++ Ψm ++ Δm)
    S = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Ψm ++ Δm))

    S₀ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    S₀ = split-++ʳ Θ (split-++ˡ s' Ξ₁)

    Sᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm) ((Ψ ++ Ξ₁) ++ Ψm ++ Δm)
    Sᶜ = split-++ˡ S₀ (Ψm ++ Δm)

    Sᴮ : Split y (Θ ++ Φ) (Θ ++ Λ ++ Ξ₁ ++ Δm) (Ψ ++ Ξ₁ ++ Δm)
    Sᴮ = split-++ʳ Θ (split-++ˡ s' (Ξ₁ ++ Δm))

    Sᴮᶜ : Split y (Θ ++ Φ) ((Θ ++ Λ ++ Ξ₁) ++ Δm) ((Ψ ++ Ξ₁) ++ Δm)
    Sᴮᶜ = split-++ˡ S₀ Δm

    Wq : Tm (Θ ++ Λ ++ Ξ₁ ++ Δm) C
    Wq = sub (split-++ˡ s₁ Δm) Q g

    W' : Tm ((Θ ++ Λ ++ Ξ₁) ++ Δm) C
    W' = cast (sym flᴮ) Wq

    W : Tm ((Θ ++ Λ ++ Ξ₁) ++ Ψm ++ Δm) C
    W = match𝟙 {Γ = Θ ++ Λ ++ Ξ₁} {Δ = Δm} P W'

    X : Tm ((Θ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δm) C
    X = sub Sᴮᶜ W' h

    Qgh : Tm (Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δm) C
    Qgh = sub (split-++ˡ s₁ Δm) Q gh

    ihQ : PathP (λ i → Tm (assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δm) i) C)
            (sub Sᴮ Wq h) Qgh
    ihQ = sub-assoc (split-++ˡ s₁ Δm) s' Q g h

    eL : sub S (sub (split-++ˡ s₁ (Ψm ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᴸ W) h
    eL = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ˡ s₁ (Ψm ++ Δm))
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᴸ)

    π : PathP (λ i → Tm ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) i) C)
          (sub Sᶜ W h) (sub S (cast flᴸ W) h)
    π i = sub (co-L Θ s' Ξ₁ (Ψm ++ Δm) i) (cast-filler flᴸ W i) h

    eC : sub Sᶜ W h
       ≡ cast qᴸ (match𝟙 {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))
    eC = ap (λ v → sub-match𝟙ˡ v P W' h) (split-++-ˡ S₀ (Ψm ++ Δm))
       ∙ cast-∙idr qᴸ (match𝟙 {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))

    eR : sub (split-++ˡ s₁ (Ψm ++ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast flᴱ (match𝟙 {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))
    eR = ap (λ v → sub-match𝟙ˡ v P Q gh) (split-++-ˡ s₁ (Ψm ++ Δm))
       ∙ cast-∙idr flᴱ (match𝟙 {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))

    innerP : PathP (λ i → Tm ((Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ Δm (~ i)) C)
               (sub Sᴮ Wq h) X
    innerP i = sub (co-L Θ s' Ξ₁ Δm (~ i)) (cast-filler (sym flᴮ) Wq i) h

    inner : PathP (λ i → Tm ((qᴮ ∙ ((ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δm)
                    ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δm)) ∙ sym flᴮᴱ)) i) C)
              (cast (sym qᴮ) X) (cast (sym flᴮᴱ) Qgh)
    inner =
      tm-∙P {P = qᴮ}
            {Q = (ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δm)
                  ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δm)) ∙ sym flᴮᴱ}
        (symP (cast-filler (sym qᴮ) X))
        (tm-∙P {P = ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δm)
                    ∙ assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δm)}
               {Q = sym flᴮᴱ}
          (tm-∙P {P = ap (λ l → (Θ ++ Φ) ++ Μ ++ l) (++-assoc Ψ Ξ₁ Δm)}
                 {Q = assocₘ-boundary Θ Φ Μ Ψ (Ξ₁ ++ Δm)}
            (symP innerP) ihQ)
          (cast-filler (sym flᴮᴱ) Qgh))

    inner' : PathP (λ i → Tm (bd₁ i ++ Δm) C)
               (cast (sym qᴮ) X) (cast (sym flᴮᴱ) Qgh)
    inner' = tm-over (sq-L-inner Θ Φ Μ Ψ Ξ₁ Δm) inner

    mid : PathP (λ i → Tm (bd₁ i ++ Ψm ++ Δm) C)
            (match𝟙 {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))
            (match𝟙 {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))
    mid i = match𝟙 {Γ = bd₁ i} {Δ = Δm} P (inner' i)

    chain : PathP (λ i → Tm ((sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) j)
                    ∙ ((sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁) ∙ flᴱ)) i) C)
              (sub S (cast flᴸ W) h)
              (cast flᴱ (match𝟙 {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh)))
    chain =
      tm-∙P {P = sym (λ j → (Θ ++ Φ) ++ Μ ++ ++-assoc Ψ Ξ₁ (Ψm ++ Δm) j)}
            {Q = (sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁) ∙ flᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᴸ ∙ ap (_++ Ψm ++ Δm) bd₁} {Q = flᴱ}
          (tm-∙P {P = sym qᴸ} {Q = ap (_++ Ψm ++ Δm) bd₁}
            (symP (cast-filler qᴸ (match𝟙 {Γ = (Θ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁} {Δ = Δm} P (cast (sym qᴮ) X))))
            mid)
          (cast-filler flᴱ (match𝟙 {Γ = Θ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁} {Δ = Δm} P (cast (sym flᴮᴱ) Qgh))))
core-m𝟙-M {x = x} {y = y} {C = C} {Θ₂ = Θ₂} {Ξ₁ = Ξ₁} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₁ s' P Q g h =
  tm-over (sq-M Γm Θ₂ Φ Μ Ψ Ξ₁ Δm) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bdᵖ : (Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁ ≡ Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁
    bdᵖ = assocₘ-boundary Θ₂ Φ Μ Ψ Ξ₁

    flᵐ : Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm ≡ (Γm ++ Θ₂) ++ Λ ++ Ξ₁ ++ Δm
    flᵐ = flattenᵐ Γm Θ₂ Λ Ξ₁ Δm

    flᵐᴱ : Γm ++ (Θ₂ ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁) ++ Δm
         ≡ (Γm ++ Θ₂) ++ (Φ ++ Μ ++ Ψ) ++ Ξ₁ ++ Δm
    flᵐᴱ = flattenᵐ Γm Θ₂ (Φ ++ Μ ++ Ψ) Ξ₁ Δm

    qᵐ : Γm ++ ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) ++ Δm
       ≡ (Γm ++ Θ₂ ++ Φ) ++ Μ ++ (Ψ ++ Ξ₁) ++ Δm
    qᵐ = flattenᵐ Γm (Θ₂ ++ Φ) Μ (Ψ ++ Ξ₁) Δm

    S : Split y ((Γm ++ Θ₂) ++ Φ) ((Γm ++ Θ₂) ++ Λ ++ Ξ₁ ++ Δm) (Ψ ++ Ξ₁ ++ Δm)
    S = split-++ʳ (Γm ++ Θ₂) (split-++ˡ s' (Ξ₁ ++ Δm))

    Sᵢ : Split y (Θ₂ ++ Φ) (Θ₂ ++ Λ ++ Ξ₁) (Ψ ++ Ξ₁)
    Sᵢ = split-++ʳ Θ₂ (split-++ˡ s' Ξ₁)

    Sᵢᶜ : Split y (Θ₂ ++ Φ) ((Θ₂ ++ Λ ++ Ξ₁) ++ Δm) ((Ψ ++ Ξ₁) ++ Δm)
    Sᵢᶜ = split-++ˡ Sᵢ Δm

    Sᶜ : Split y (Γm ++ Θ₂ ++ Φ) (Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm) ((Ψ ++ Ξ₁) ++ Δm)
    Sᶜ = split-++ʳ Γm Sᵢᶜ

    W₁ : Tm (Θ₂ ++ Λ ++ Ξ₁) 𝟙
    W₁ = sub s₁ P g

    W : Tm (Γm ++ (Θ₂ ++ Λ ++ Ξ₁) ++ Δm) C
    W = match𝟙 {Γ = Γm} {Δ = Δm} W₁ Q

    ihL : Tm ((Θ₂ ++ Φ) ++ Μ ++ Ψ ++ Ξ₁) 𝟙
    ihL = sub Sᵢ W₁ h

    ih : PathP (λ i → Tm (bdᵖ i) 𝟙) ihL (sub s₁ P gh)
    ih = sub-assoc s₁ s' P g h

    eL : sub S (sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast flᵐ W) h
    eL = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ʳ Γm (split-++ˡ s₁ Δm))
       ∙ ap (λ v → sub S (sub-match𝟙ʳ v refl P Q g) h) (split-++-ˡ s₁ Δm)
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr flᵐ)

    π : PathP (λ i → Tm (sym (++-assoc Γm Θ₂ Φ) i ++ Μ ++ ++-assoc Ψ Ξ₁ Δm i) C)
          (sub Sᶜ W h) (sub S (cast flᵐ W) h)
    π i = sub (co-M Γm Θ₂ s' Ξ₁ Δm i) (cast-filler flᵐ W i) h

    eC : sub Sᶜ W h ≡ cast qᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)
    eC = ap (λ v → sub-match𝟙ˡ v W₁ Q h) (split-++-ʳ Γm Sᵢᶜ)
       ∙ ap (λ v → sub-match𝟙ʳ v refl W₁ Q h) (split-++-ˡ Sᵢ Δm)
       ∙ cast-∙idr qᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)

    eR : sub (split-++ʳ Γm (split-++ˡ s₁ Δm)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast flᵐᴱ (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)
    eR = ap (λ v → sub-match𝟙ˡ v P Q gh) (split-++-ʳ Γm (split-++ˡ s₁ Δm))
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Q gh) (split-++-ˡ s₁ Δm)
       ∙ cast-∙idr flᵐᴱ (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)

    mid : PathP (λ i → Tm (Γm ++ bdᵖ i ++ Δm) C)
            (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)
            (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)
    mid i = match𝟙 {Γ = Γm} {Δ = Δm} (ih i) Q

    chain : PathP (λ i → Tm ((sym (λ j → sym (++-assoc Γm Θ₂ Φ) j ++ Μ ++ ++-assoc Ψ Ξ₁ Δm j)
                    ∙ ((sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ) ∙ flᵐᴱ)) i) C)
              (sub S (cast flᵐ W) h)
              (cast flᵐᴱ (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q))
    chain =
      tm-∙P {P = sym (λ j → sym (++-assoc Γm Θ₂ Φ) j ++ Μ ++ ++-assoc Ψ Ξ₁ Δm j)}
            {Q = (sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ) ∙ flᵐᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᵐ ∙ ap (λ l → Γm ++ l ++ Δm) bdᵖ} {Q = flᵐᴱ}
          (tm-∙P {P = sym qᵐ} {Q = ap (λ l → Γm ++ l ++ Δm) bdᵖ}
            (symP (cast-filler qᵐ (match𝟙 {Γ = Γm} {Δ = Δm} ihL Q)))
            mid)
          (cast-filler flᵐᴱ (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P gh) Q)))
core-m𝟙-B {x = x} {y = y} {C = C} {Θ₃ = Θ₃} {Ξ = Ξ} {Γm = Γm}
  {Ψm = Ψm} {Δm = Δm} {Φ = Φ} {Λ = Λ} {Ψ = Ψ} {Μ = Μ} s₂ s' P Q g h =
  tm-over (sq-B Γm Ψm Θ₃ Φ Μ Ψ Ξ) (eL ◁ chain ▷ sym eR)
  where
    gh : Tm (Φ ++ Μ ++ Ψ) x
    gh = sub s' g h

    bd₃ : (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bd₃ = assocₘ-boundary Θ₃ Φ Μ Ψ Ξ

    bdᴮ : ((Γm ++ Θ₃) ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ (Γm ++ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    bdᴮ = assocₘ-boundary (Γm ++ Θ₃) Φ Μ Ψ Ξ

    bu : Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ ≡ (Γm ++ Ψm ++ Θ₃) ++ Λ ++ Ξ
    bu = bury Γm Ψm Θ₃ (Λ ++ Ξ)

    buᴱ : Γm ++ Ψm ++ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ
        ≡ (Γm ++ Ψm ++ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    buᴱ = bury Γm Ψm Θ₃ ((Φ ++ Μ ++ Ψ) ++ Ξ)

    qᵇ : Γm ++ Ψm ++ (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
       ≡ (Γm ++ Ψm ++ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qᵇ = bury Γm Ψm (Θ₃ ++ Φ) (Μ ++ Ψ ++ Ξ)

    flʳᴮ : Γm ++ Θ₃ ++ Λ ++ Ξ ≡ (Γm ++ Θ₃) ++ Λ ++ Ξ
    flʳᴮ = flattenʳ Γm Θ₃ Λ Ξ

    flʳᴮᴱ : Γm ++ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ ≡ (Γm ++ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ
    flʳᴮᴱ = flattenʳ Γm Θ₃ (Φ ++ Μ ++ Ψ) Ξ

    qʳᴮ : Γm ++ (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ ≡ (Γm ++ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ
    qʳᴮ = flattenʳ Γm (Θ₃ ++ Φ) Μ (Ψ ++ Ξ)

    S : Split y ((Γm ++ Ψm ++ Θ₃) ++ Φ) ((Γm ++ Ψm ++ Θ₃) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    S = split-++ʳ (Γm ++ Ψm ++ Θ₃) (split-++ˡ s' Ξ)

    Sᵣ' : Split y (Θ₃ ++ Φ) (Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᵣ' = split-++ʳ Θ₃ (split-++ˡ s' Ξ)

    Sᵣ : Split y (Ψm ++ Θ₃ ++ Φ) (Ψm ++ Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᵣ = split-++ʳ Ψm Sᵣ'

    Sᶜ : Split y (Γm ++ Ψm ++ Θ₃ ++ Φ) (Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᶜ = split-++ʳ Γm Sᵣ

    Sᴮ : Split y ((Γm ++ Θ₃) ++ Φ) ((Γm ++ Θ₃) ++ Λ ++ Ξ) (Ψ ++ Ξ)
    Sᴮ = split-++ʳ (Γm ++ Θ₃) (split-++ˡ s' Ξ)

    sq : Split x (Γm ++ Θ₃) (Γm ++ Δm) Ξ
    sq = split-++ʳ Γm s₂

    Wq : Tm ((Γm ++ Θ₃) ++ Λ ++ Ξ) C
    Wq = sub sq Q g

    W' : Tm (Γm ++ Θ₃ ++ Λ ++ Ξ) C
    W' = cast (sym flʳᴮ) Wq

    W : Tm (Γm ++ Ψm ++ Θ₃ ++ Λ ++ Ξ) C
    W = match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Λ ++ Ξ} P W'

    X : Tm ((Γm ++ Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ) C
    X = sub (split-++ʳ Γm Sᵣ') W' h

    Qgh : Tm ((Γm ++ Θ₃) ++ (Φ ++ Μ ++ Ψ) ++ Ξ) C
    Qgh = sub sq Q gh

    Wq' : Tm (Γm ++ Ψm ++ (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ) C
    Wq' = match𝟙 {Γ = Γm} {Δ = (Θ₃ ++ Φ) ++ Μ ++ Ψ ++ Ξ} P (cast (sym qʳᴮ) X)

    Wᴱ : Tm (Γm ++ Ψm ++ Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ) C
    Wᴱ = match𝟙 {Γ = Γm} {Δ = Θ₃ ++ (Φ ++ Μ ++ Ψ) ++ Ξ} P (cast (sym flʳᴮᴱ) Qgh)

    ihQ : PathP (λ i → Tm (bdᴮ i) C) (sub Sᴮ Wq h) Qgh
    ihQ = sub-assoc sq s' Q g h

    eL : sub S (sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) g) h
       ≡ sub S (cast bu W) h
    eL = ap (λ v → sub S (sub-match𝟙ˡ v P Q g) h) (split-++-ʳ Γm (split-++ʳ Ψm s₂))
       ∙ ap (λ v → sub S (sub-match𝟙ʳ v refl P Q g) h) (split-++-ʳ Ψm s₂)
       ∙ ap (λ w → sub S (cast (bu ∙ ap (_++ Λ ++ Ξ) w) W) h)
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃}))
       ∙ ap (λ ρ → sub S (cast ρ W) h) (∙-idr bu)

    π : PathP (λ i → Tm (bury Γm Ψm Θ₃ Φ i ++ Μ ++ Ψ ++ Ξ) C)
          (sub Sᶜ W h) (sub S (cast bu W) h)
    π i = sub (co-B Γm Ψm Θ₃ s' Ξ i) (cast-filler bu W i) h

    eC : sub Sᶜ W h ≡ cast qᵇ Wq'
    eC = ap (λ v → sub-match𝟙ˡ v P W' h) (split-++-ʳ Γm Sᵣ)
       ∙ ap (λ v → sub-match𝟙ʳ v refl P W' h) (split-++-ʳ Ψm Sᵣ')
       ∙ ap (λ w → cast (qᵇ ∙ ap (_++ Μ ++ Ψ ++ Ξ) w) Wq')
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃ ++ Φ}))
       ∙ cast-∙idr qᵇ Wq'

    eR : sub (split-++ʳ Γm (split-++ʳ Ψm s₂)) (match𝟙 {Γ = Γm} {Δ = Δm} P Q) gh
       ≡ cast buᴱ Wᴱ
    eR = ap (λ v → sub-match𝟙ˡ v P Q gh) (split-++-ʳ Γm (split-++ʳ Ψm s₂))
       ∙ ap (λ v → sub-match𝟙ʳ v refl P Q gh) (split-++-ʳ Ψm s₂)
       ∙ ap (λ w → cast (buᴱ ∙ ap (_++ (Φ ++ Μ ++ Ψ) ++ Ξ) w) Wᴱ)
            (∙-idr (refl {x = Γm ++ Ψm ++ Θ₃}))
       ∙ cast-∙idr buᴱ Wᴱ

    innerP : PathP (λ i → Tm (++-assoc Γm Θ₃ Φ i ++ Μ ++ Ψ ++ Ξ) C)
               (sub Sᴮ Wq h) X
    innerP i = sub (co-R Γm Θ₃ s' Ξ (~ i)) (cast-filler (sym flʳᴮ) Wq i) h

    inner : PathP (λ i → Tm ((qʳᴮ ∙ ((ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ))
                    ∙ bdᴮ) ∙ sym flʳᴮᴱ)) i) C)
              (cast (sym qʳᴮ) X) (cast (sym flʳᴮᴱ) Qgh)
    inner =
      tm-∙P {P = qʳᴮ}
            {Q = (ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ)) ∙ bdᴮ) ∙ sym flʳᴮᴱ}
        (symP (cast-filler (sym qʳᴮ) X))
        (tm-∙P {P = ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ)) ∙ bdᴮ}
               {Q = sym flʳᴮᴱ}
          (tm-∙P {P = ap (_++ Μ ++ Ψ ++ Ξ) (sym (++-assoc Γm Θ₃ Φ))}
                 {Q = bdᴮ}
            (symP innerP) ihQ)
          (cast-filler (sym flʳᴮᴱ) Qgh))

    inner' : PathP (λ i → Tm (Γm ++ bd₃ i) C)
               (cast (sym qʳᴮ) X) (cast (sym flʳᴮᴱ) Qgh)
    inner' = tm-over (sq-B-inner𝟙 Γm Θ₃ Φ Μ Ψ Ξ) inner

    mid : PathP (λ i → Tm (Γm ++ Ψm ++ bd₃ i) C) Wq' Wᴱ
    mid i = match𝟙 {Γ = Γm} {Δ = bd₃ i} P (inner' i)

    chain : PathP (λ i → Tm ((sym (λ j → bury Γm Ψm Θ₃ Φ j ++ Μ ++ Ψ ++ Ξ)
                    ∙ ((sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃) ∙ buᴱ)) i) C)
              (sub S (cast bu W) h) (cast buᴱ Wᴱ)
    chain =
      tm-∙P {P = sym (λ j → bury Γm Ψm Θ₃ Φ j ++ Μ ++ Ψ ++ Ξ)}
            {Q = (sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃) ∙ buᴱ}
        (symP π ▷ eC)
        (tm-∙P {P = sym qᵇ ∙ ap (λ l → Γm ++ Ψm ++ l) bd₃} {Q = buᴱ}
          (tm-∙P {P = sym qᵇ} {Q = ap (λ l → Γm ++ Ψm ++ l) bd₃}
            (symP (cast-filler qᵇ Wq'))
            mid)
          (cast-filler buᴱ Wᴱ))
