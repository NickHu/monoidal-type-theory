open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
open import Multicategory.Free
open import Multicategory.Functor using (map-++₂)
import Multicategory.Representable as Rep
import Multicategory.Free.Eval as EvalMod

-- Freeness laws for the evaluation of the simple type theory into a
-- representable premulticategory M (Shulman, Theorem 2.4.10): eval maps sub
-- to _∘ₘ_ (Tier 1), respects the β/η congruence (Tier 2), and descends to a
-- multifunctor FMonCat G → M (Tier 3).

module Multicategory.Free.Freeness
  {o h o' h'} (G : Multigraph o h)
  (M : Premulticategory o' h') (rep : Rep.is-representable M)
  (φ : EvalMod.Multigraph-hom↓ G M rep)
  where

open import Multicategory.Free.SplitLemmas G

private
  module G = Multigraph G
  module M = Premulticategory M
  module E = EvalMod G M rep
  module φ = E.Multigraph-hom↓ φ

open E using (⊗M ; uM ; uM-universal ; castₘ ; unplug)

-- φ-specialised aliases for the evaluation machinery (transparent, so all of
-- eval's clause equations still hold definitionally through them).
⟦_⟧ᵗ : Ty → M.Obₘ
⟦_⟧ᵗ = E.⟦_⟧ᵗ φ

⟦_⟧ᶜ : Ctx → List M.Obₘ
⟦_⟧ᶜ = E.⟦_⟧ᶜ φ

⟦⟧-++ : (Γ Δ : Ctx) → ⟦ Γ ++ Δ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ++ ⟦ Δ ⟧ᶜ
⟦⟧-++ = E.⟦⟧-++ φ

⟦⟧-++₂ : (Γ Ψ Δ : Ctx) → ⟦ Γ ++ Ψ ++ Δ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δ ⟧ᶜ
⟦⟧-++₂ = E.⟦⟧-++₂ φ

sp-step-path : (Χ : List M.Obₘ) (Γ₁ Δ : Ctx)
             → (Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Δ ⟧ᶜ ≡ Χ ++ ⟦ Γ₁ ++ Δ ⟧ᶜ
sp-step-path = E.sp-step-path φ

pair-path : (Γ₁ Δ₁ : Ctx) → ⟦ Γ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ [] ≡ ⟦ Γ₁ ++ Δ₁ ⟧ᶜ
pair-path = E.pair-path φ

eval : ∀ {Γ : Ctx} {z : Ty} → Tm Γ z → M.Homₘ ⟦ Γ ⟧ᶜ ⟦ z ⟧ᵗ
eval = E.eval φ

eval-sp : ∀ {As : List G.Ob} {Δ : Ctx} {w : M.Obₘ} (Χ : List M.Obₘ)
        → M.Homₘ (Χ ++ map φ.F₀ As) w → Sp Δ As → M.Homₘ (Χ ++ ⟦ Δ ⟧ᶜ) w
eval-sp = E.eval-sp φ

private variable
  x y z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Λ Μ Κ Γ₁ Γ₂ Δ₁ Ξ₁ Θ₂ Φ : Ctx
  As : List G.Ob
  w : M.Obₘ

-- ==========================================================================
-- Tier 1, part 0: the slot path of a split, interpreted in M.  Structural
-- (cons-by-cons); the base case is refl since ⟦ x ∷ Ξ ⟧ᶜ is definitionally
-- ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ.
-- ==========================================================================

⟦split⟧ : Split x Θ Ρ Ξ → ⟦ Ρ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
⟦split⟧ here      = refl
⟦split⟧ (there {a = a} s) = ap (⟦ a ⟧ᵗ ∷_) (⟦split⟧ s)

-- ==========================================================================
-- M-level transport kit (the Homₘ analogues of Kit/Identity's cast
-- machinery): fillers, base-path reconciliation, PathP composition over
-- ∙-composite bases, and cast eliminators.
-- ==========================================================================

private variable
  Ω₀ Ω₁ Ω₂ : List M.Obₘ
  u v : M.Obₘ

castₘ-filler : (p : Ω₀ ≡ Ω₁) (f : M.Homₘ Ω₀ w)
             → PathP (λ i → M.Homₘ (p i) w) f (castₘ p f)
castₘ-filler {w = w} p f = transport-filler (λ i → M.Homₘ (p i) w) f

hom-over : {p q : Ω₀ ≡ Ω₁} (α : p ≡ q) {f : M.Homₘ Ω₀ w} {g : M.Homₘ Ω₁ w}
         → PathP (λ i → M.Homₘ (p i) w) f g → PathP (λ i → M.Homₘ (q i) w) f g
hom-over {w = w} α {f} {g} = subst (λ p → PathP (λ i → M.Homₘ (p i) w) f g) α

hom-∙P : {P : Ω₀ ≡ Ω₁} {Q : Ω₁ ≡ Ω₂}
         {f : M.Homₘ Ω₀ w} {g : M.Homₘ Ω₁ w} {k : M.Homₘ Ω₂ w}
       → PathP (λ i → M.Homₘ (P i) w) f g
       → PathP (λ i → M.Homₘ (Q i) w) g k
       → PathP (λ i → M.Homₘ ((P ∙ Q) i) w) f k
hom-∙P {w = w} {P = P} {Q = Q} {f = f} {g = g} {k = k} p q i =
  comp (λ j → M.Homₘ (∙-filler P Q j i) w) (∂ i) λ where
    j (j = i0) → p i
    j (i = i0) → f
    j (i = i1) → q j

-- One-dimensional path algebra, verbatim from Identity.agda (coherences
-- BETWEEN structural paths, so ∙-composites are fine inside them).
private
  square→∙ˡ : ∀ {ℓ} {X : Type ℓ} {a b c : X} {L : a ≡ b} {u' : a ≡ c} {v' : b ≡ c}
            → PathP (λ k → L k ≡ c) u' v' → L ∙ v' ≡ u'
  square→∙ˡ {u' = u'} sq = square→commutes sq ∙ ∙-idr u'

  flip-cancel : ∀ {ℓ} {X : Type ℓ} {a b c : X} (p : a ≡ b) {d : a ≡ c} {e : b ≡ c}
              → p ∙ e ≡ d → sym p ∙ d ≡ e
  flip-cancel p θ = ap (sym p ∙_) (sym θ) ∙ ∙-cancell p _

  θ-step : ∀ {ℓ} {X : Type ℓ} {a b c d' : X} (F : a ≡ b)
           {w' : b ≡ c} {v' : c ≡ d'} {u' : b ≡ d'} {r : a ≡ d'}
         → PathP (λ k → w' k ≡ d') u' v'
         → F ∙ u' ≡ r
         → (F ∙ w') ∙ v' ≡ r
  θ-step F {w' = w'} {v' = v'} sq δ =
    sym (∙-assoc F w' v') ∙ ap (F ∙_) (square→∙ˡ sq) ∙ δ

  θ-step₂ : ∀ {ℓ} {X : Type ℓ} {a b c c' d' : X} (F : a ≡ b)
            {w₂ : b ≡ c} {w₁ : c ≡ c'} {v' : c' ≡ d'}
            {m₂ : c ≡ d'} {u' : b ≡ d'} {r : a ≡ d'}
          → PathP (λ k → w₁ k ≡ d') m₂ v'
          → PathP (λ k → w₂ k ≡ d') u' m₂
          → F ∙ u' ≡ r
          → (F ∙ (w₂ ∙ w₁)) ∙ v' ≡ r
  θ-step₂ F {w₂ = w₂} {w₁ = w₁} {v' = v'} sq₁ sq₂ δ =
    sym (∙-assoc F (w₂ ∙ w₁) v')
    ∙ ap (F ∙_) (sym (∙-assoc w₂ w₁ v') ∙ ap (w₂ ∙_) (square→∙ˡ sq₁) ∙ square→∙ˡ sq₂)
    ∙ δ

  ap-∙-step : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c : X}
              {p : a ≡ b} {q : b ≡ c} {r : a ≡ c}
            → p ∙ q ≡ r → ap f p ∙ ap f q ≡ ap f r
  ap-∙-step f {p = p} {q = q} eq = sym (ap-∙ f p q) ∙ ap (ap f) eq

  diag-∙ : ∀ {ℓa ℓb ℓc} {X : Type ℓa} {Y : Type ℓb} {Z : Type ℓc}
           (f : X → Y → Z) {a a' : X} {b b' : Y} (q : a ≡ a') (p : b ≡ b')
         → (λ i → f (q i) (p i)) ≡ (λ i → f a (p i)) ∙ (λ i → f (q i) b')
  diag-∙ f q p = ∙-unique _ λ i j → f (q (i ∧ j)) (p j)

-- Cast eliminators: peel a castₘ (or an eval'd syntactic cast) off an
-- endpoint of a Homₘ PathP, moving the base path by an α given in either
-- orientation.
private
  castₘ-step : (c : Ω₀ ≡ Ω₁) {d : Ω₀ ≡ Ω₂} {e : Ω₁ ≡ Ω₂}
               {f : M.Homₘ Ω₀ w} {g : M.Homₘ Ω₂ w}
             → PathP (λ i → M.Homₘ (d i) w) f g
             → sym c ∙ d ≡ e
             → PathP (λ i → M.Homₘ (e i) w) (castₘ c f) g
  castₘ-step c {d = d} {f = f} h α =
    hom-over α (hom-∙P {P = sym c} {Q = d} (symP (castₘ-filler c f)) h)

  castₘ-out : (c : Ω₀ ≡ Ω₁) {d : Ω₀ ≡ Ω₂} {e : Ω₁ ≡ Ω₂}
              {f : M.Homₘ Ω₀ w} {g : M.Homₘ Ω₂ w}
            → PathP (λ i → M.Homₘ (d i) w) f g
            → c ∙ e ≡ d
            → PathP (λ i → M.Homₘ (e i) w) (castₘ c f) g
  castₘ-out c h θ = castₘ-step c h (flip-cancel c θ)

-- eval commutes with the syntactic cast: eval applied under the interval to
-- the cast filler (no J anywhere).
eval-cast : (p : Ρ ≡ Γ) (t : Tm Ρ z)
          → PathP (λ i → M.Homₘ ⟦ p i ⟧ᶜ ⟦ z ⟧ᵗ) (eval t) (eval (cast p t))
eval-cast p t i = eval (cast-filler p t i)

eval-sp-cast : (Χ : List M.Obₘ) (f : M.Homₘ (Χ ++ map φ.F₀ As) w)
               (p : Ρ ≡ Γ) (ts : Sp Ρ As)
             → PathP (λ i → M.Homₘ (Χ ++ ⟦ p i ⟧ᶜ) w)
                 (eval-sp Χ f ts) (eval-sp Χ f (sp-cast p ts))
eval-sp-cast Χ f p ts i = eval-sp Χ f (sp-cast-filler p ts i)

-- ==========================================================================
-- Prefix-generalised boundary paths for the spine lemma (all structural,
-- cons-by-cons on the ambient prefix Χ).
-- ==========================================================================

-- Push a slot decomposition under an ambient prefix.
pre-split : (Χ : List M.Obₘ) {Λ' Θ' Ξ' : List M.Obₘ} {x' : M.Obₘ}
          → Λ' ≡ Θ' ++ x' ∷ Ξ' → Χ ++ Λ' ≡ (Χ ++ Θ') ++ x' ∷ Ξ'
pre-split []      p = p
pre-split (a ∷ Χ) p = ap (a ∷_) (pre-split Χ p)

-- The eval-sub boundary under an ambient prefix.
pre-bound : (Χ : List M.Obₘ) (Θ Γ Ξ : Ctx)
          → Χ ++ ⟦ Θ ++ Γ ++ Ξ ⟧ᶜ ≡ (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ
pre-bound []      Θ Γ Ξ = ⟦⟧-++₂ Θ Γ Ξ
pre-bound (a ∷ Χ) Θ Γ Ξ = ap (a ∷_) (pre-bound Χ Θ Γ Ξ)

-- Fully left-nest a four-part concatenation whose middle got replaced.
nest₂ : (Χ₁ Λ' Χ₂ N : List M.Obₘ)
      → Χ₁ ++ Λ' ++ (Χ₂ ++ N) ≡ ((Χ₁ ++ Λ') ++ Χ₂) ++ N
nest₂ []       Λ' Χ₂ N = sym (++-assoc Λ' Χ₂ N)
nest₂ (a ∷ Χ₁) Λ' Χ₂ N = ap (a ∷_) (nest₂ Χ₁ Λ' Χ₂ N)

-- ==========================================================================
-- Base-path square for the var case: ⟦_⟧ᶜ of ++-idr, undone at the M level,
-- is the ++-homomorphism path at the empty suffix.
-- ==========================================================================

private
  mapf-idr : ∀ (Γ : Ctx)
           → ap ⟦_⟧ᶜ (++-idr Γ) ∙ sym (++-idr ⟦ Γ ⟧ᶜ) ≡ ⟦⟧-++ Γ []
  mapf-idr []      = ∙-idr refl
  mapf-idr (A ∷ Γ) =
    ap-∙-step (⟦ A ⟧ᵗ ∷_)
      {p = ap ⟦_⟧ᶜ (++-idr Γ)} {q = sym (++-idr ⟦ Γ ⟧ᶜ)}
      (mapf-idr Γ)

-- ==========================================================================
-- Tier 1, the var case: substituting into a variable is idₘr in M, with the
-- vacuous cast castₘ refl (eval var) peeled by transport-refl.
-- ==========================================================================

eval-sub-var : ∀ {z Γ x Θ Ξ} (s : Split x Θ (z ∷ []) Ξ) (g : Tm Γ x)
             → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ z ⟧ᵗ)
                 (eval (sub-var s g))
                 (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                   (castₘ (⟦split⟧ s) (eval (var {A = z}))) (eval g))
eval-sub-var {z = z} {Γ = Γ} here g =
  hom-over
    ( ap (ap ⟦_⟧ᶜ (++-idr Γ) ∙_) (∙-idr (sym (++-idr ⟦ Γ ⟧ᶜ)))
    ∙ mapf-idr Γ )
    (hom-∙P (symP (eval-cast (sym (++-idr Γ)) g))
      (hom-∙P (symP (M.idₘr (eval g)))
        (ap (λ k → M._∘ₘ_ {Θ = []} {Ξ = []} k (eval g))
          (sym (transport-refl M.idₘ)))))
eval-sub-var (there s) g = absurd (split-[] s)

-- ==========================================================================
-- More kit: two casts of the same hom compared over a reconciled base, and
-- eval-sp applied under the interval in its prefix/hom arguments.
-- ==========================================================================

cast-vs-cast : (p : Ω₀ ≡ Ω₁) (q : Ω₀ ≡ Ω₂) (f : M.Homₘ Ω₀ w) {e : Ω₁ ≡ Ω₂}
             → sym p ∙ q ≡ e
             → PathP (λ i → M.Homₘ (e i) w) (castₘ p f) (castₘ q f)
cast-vs-cast p q f α =
  hom-over α (hom-∙P {P = sym p} {Q = q}
    (symP (castₘ-filler p f)) (castₘ-filler q f))

eval-sp-over : {Χ Χ' : List M.Obₘ} (ρ : Χ ≡ Χ')
               {f : M.Homₘ (Χ ++ map φ.F₀ As) w}
               {f' : M.Homₘ (Χ' ++ map φ.F₀ As) w}
             → PathP (λ i → M.Homₘ (ρ i ++ map φ.F₀ As) w) f f'
             → (ts : Sp Δ As)
             → PathP (λ i → M.Homₘ (ρ i ++ ⟦ Δ ⟧ᶜ) w)
                 (eval-sp Χ f ts) (eval-sp Χ' f' ts)
eval-sp-over ρ F ts i = eval-sp (ρ i) (F i) ts

-- Right-nested ap-distribution at arities 3-5 (cons steps of the base-path
-- squares below; chains are canonically nested a ∙ (b ∙ (c ∙ …))).
private
  ∙-ap₂' : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c : X}
           (p : a ≡ b) (q : b ≡ c)
         → ap f p ∙ ap f q ≡ ap f (p ∙ q)
  ∙-ap₂' f p q = sym (ap-∙ f p q)

  ∙-ap₃ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d : X}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → ap f p ∙ (ap f q ∙ ap f r) ≡ ap f (p ∙ (q ∙ r))
  ∙-ap₃ f p q r = ap (ap f p ∙_) (∙-ap₂' f q r) ∙ ∙-ap₂' f p (q ∙ r)

  ∙-ap₄ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e : X}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
        → ap f p ∙ (ap f q ∙ (ap f r ∙ ap f s)) ≡ ap f (p ∙ (q ∙ (r ∙ s)))
  ∙-ap₄ f p q r s = ap (ap f p ∙_) (∙-ap₃ f q r s) ∙ ∙-ap₂' f p (q ∙ (r ∙ s))

  ∙-ap₅ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e g' : X}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ g')
        → ap f p ∙ (ap f q ∙ (ap f r ∙ (ap f s ∙ ap f t)))
        ≡ ap f (p ∙ (q ∙ (r ∙ (s ∙ t))))
  ∙-ap₅ f p q r s t =
    ap (ap f p ∙_) (∙-ap₄ f q r s t) ∙ ∙-ap₂' f p (q ∙ (r ∙ (s ∙ t)))

  -- Cons steps for the structural base-path squares: distribute the ap over
  -- the chain's canonical nesting, then apply the inductive hypothesis.
  sq-stepᵣ₄ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) {u : a ≡ e}
            → p ∙ (q ∙ (r ∙ s)) ≡ u
            → ap f p ∙ (ap f q ∙ (ap f r ∙ ap f s)) ≡ ap f u
  sq-stepᵣ₄ f p q r s eq = ∙-ap₄ f p q r s ∙ ap (ap f) eq

  sq-stepᵣ₅ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e e' : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ e')
              {u : a ≡ e'}
            → p ∙ (q ∙ (r ∙ (s ∙ t))) ≡ u
            → ap f p ∙ (ap f q ∙ (ap f r ∙ (ap f s ∙ ap f t))) ≡ ap f u
  sq-stepᵣ₅ f p q r s t eq = ∙-ap₅ f p q r s t ∙ ap (ap f) eq

  -- Two-sided cons step: LHS a 2-chain, RHS a right-nested 3-chain.
  sq-step₂₃ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c a' b' : X}
              (p : a ≡ b) (q : b ≡ c) (r : a ≡ a') (s : a' ≡ b') (t : b' ≡ c)
            → p ∙ q ≡ r ∙ (s ∙ t)
            → ap f p ∙ ap f q ≡ ap f r ∙ (ap f s ∙ ap f t)
  sq-step₂₃ f p q r s t eq =
    ∙-ap₂' f p q ∙ ap (ap f) eq ∙ sym (∙-ap₃ f r s t)

  -- Shape a ∙ ((b ∙ c) ∙ d) (as in Assoc's ∙-ap-sh).
  ∙-ap-sh : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {v w' x' y' z' : X}
            (a : v ≡ w') (b : w' ≡ x') (c : x' ≡ y') (d : y' ≡ z')
          → ap f a ∙ ((ap f b ∙ ap f c) ∙ ap f d)
          ≡ ap f (a ∙ ((b ∙ c) ∙ d))
  ∙-ap-sh f a b c d =
      ap (ap f a ∙_) (ap (_∙ ap f d) (∙-ap₂' f b c) ∙ ∙-ap₂' f (b ∙ c) d)
    ∙ ∙-ap₂' f a ((b ∙ c) ∙ d)

  sq-step-sh : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {v w' x' y' z' : X}
               (a : v ≡ w') (b : w' ≡ x') (c : x' ≡ y') (d : y' ≡ z') {u : v ≡ z'}
             → a ∙ ((b ∙ c) ∙ d) ≡ u
             → ap f a ∙ ((ap f b ∙ ap f c) ∙ ap f d) ≡ ap f u
  sq-step-sh f a b c d eq = ∙-ap-sh f a b c d ∙ ap (ap f) eq

-- ==========================================================================
-- Base-path squares for plug-sp.  All structural inductions; cons steps are
-- the sq-step helpers, bases are groupoid algebra.
-- ==========================================================================

private
  -- sp-step-path unfolded: reassociate, then rewrite the tail by the
  -- ++-homomorphism path.
  sq-sp-step : ∀ (Χ : List M.Obₘ) (Γ₁ Δ : Ctx)
             → sp-step-path Χ Γ₁ Δ
             ≡ ++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ ++_) (sym (⟦⟧-++ Γ₁ Δ))
  sq-sp-step []      Γ₁ Δ = sym (∙-idl (sym (⟦⟧-++ Γ₁ Δ)))
  sq-sp-step (a ∷ Χ) Γ₁ Δ =
      ap (ap (a ∷_)) (sq-sp-step Χ Γ₁ Δ)
    ∙ ap-∙ (a ∷_) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ) (ap (Χ ++_) (sym (⟦⟧-++ Γ₁ Δ)))

  -- The nest₂ path against interchange-slot₁, over reassociating the prefix.
  sq-nest-slot₁ : ∀ (Χ₁ Λ' Χ₂ : List M.Obₘ) (y : M.Obₘ) (N' : List M.Obₘ)
                → sym (nest₂ Χ₁ Λ' Χ₂ (y ∷ N')) ∙ interchange-slot₁ Χ₁ Λ' Χ₂ y N'
                ≡ ap (_++ (y ∷ N')) (++-assoc Χ₁ Λ' Χ₂)
  sq-nest-slot₁ []       Λ' Χ₂ y N' = ∙-invr (++-assoc Λ' Χ₂ (y ∷ N'))
  sq-nest-slot₁ (a ∷ Χ₁) Λ' Χ₂ y N' =
    ap-∙-step (a ∷_)
      {p = sym (nest₂ Χ₁ Λ' Χ₂ (y ∷ N'))} {q = interchange-slot₁ Χ₁ Λ' Χ₂ y N'}
      (sq-nest-slot₁ Χ₁ Λ' Χ₂ y N')

  -- The pentagon-flavoured square for the middle chain of plug-sp's cons
  -- case (level 2: induction on Λ' once the ambient Χ₁ is gone).
  sq-F₀ : ∀ (Λ' Χ₂ C1 N' : List M.Obₘ)
        → ++-assoc (Λ' ++ Χ₂) C1 N'
          ∙ (refl
          ∙ (++-assoc Λ' Χ₂ (C1 ++ N')
          ∙ (ap (λ l → Λ' ++ l) (sym (++-assoc Χ₂ C1 N'))
          ∙ sym (++-assoc Λ' (Χ₂ ++ C1) N'))))
        ≡ ap (_++ N') (++-assoc Λ' Χ₂ C1)
  sq-F₀ [] Χ₂ C1 N' =
      ap (++-assoc Χ₂ C1 N' ∙_)
        ( ∙-idl (refl ∙ (sym (++-assoc Χ₂ C1 N') ∙ refl))
        ∙ ∙-idl (sym (++-assoc Χ₂ C1 N') ∙ refl)
        ∙ ∙-idr (sym (++-assoc Χ₂ C1 N')) )
    ∙ ∙-invr (++-assoc Χ₂ C1 N')
  sq-F₀ (a ∷ Λ') Χ₂ C1 N' =
    sq-stepᵣ₅ (a ∷_)
      (++-assoc (Λ' ++ Χ₂) C1 N') refl (++-assoc Λ' Χ₂ (C1 ++ N'))
      (ap (λ l → Λ' ++ l) (sym (++-assoc Χ₂ C1 N')))
      (sym (++-assoc Λ' (Χ₂ ++ C1) N'))
      (sq-F₀ Λ' Χ₂ C1 N')

  sq-F : ∀ (Χ₁ Λ' Χ₂ C1 N' : List M.Obₘ)
       → ++-assoc ((Χ₁ ++ Λ') ++ Χ₂) C1 N'
         ∙ (ap (_++ (C1 ++ N')) (++-assoc Χ₁ Λ' Χ₂)
         ∙ (interchangeₘ-boundary Χ₁ Λ' Χ₂ C1 N'
         ∙ (ap (λ l → Χ₁ ++ Λ' ++ l) (sym (++-assoc Χ₂ C1 N'))
         ∙ nest₂ Χ₁ Λ' (Χ₂ ++ C1) N')))
       ≡ ap (_++ N') (++-assoc (Χ₁ ++ Λ') Χ₂ C1)
  sq-F [] Λ' Χ₂ C1 N' = sq-F₀ Λ' Χ₂ C1 N'
  sq-F (a ∷ Χ₁) Λ' Χ₂ C1 N' =
    sq-stepᵣ₅ (a ∷_)
      (++-assoc ((Χ₁ ++ Λ') ++ Χ₂) C1 N')
      (ap (_++ (C1 ++ N')) (++-assoc Χ₁ Λ' Χ₂))
      (interchangeₘ-boundary Χ₁ Λ' Χ₂ C1 N')
      (ap (λ l → Χ₁ ++ Λ' ++ l) (sym (++-assoc Χ₂ C1 N')))
      (nest₂ Χ₁ Λ' (Χ₂ ++ C1) N')
      (sq-F Χ₁ Λ' Χ₂ C1 N')

  -- The square behind the inner-hom bridge G of plug-sp's cons case.
  sq-G : ∀ (Χ₁ : List M.Obₘ) (x' : M.Obₘ) (Χ₂ C1 N' : List M.Obₘ)
       → ++-assoc (Χ₁ ++ x' ∷ Χ₂) C1 N'
         ∙ ((++-assoc Χ₁ (x' ∷ Χ₂) (C1 ++ N')
             ∙ ap (λ l → Χ₁ ++ x' ∷ l) (sym (++-assoc Χ₂ C1 N')))
            ∙ sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) N'))
       ≡ ap (_++ N') (++-assoc Χ₁ (x' ∷ Χ₂) C1)
  sq-G [] x' Χ₂ C1 N' =
      ap (ap (x' ∷_) (++-assoc Χ₂ C1 N') ∙_)
        ( ap (_∙ refl) (∙-idl (ap (x' ∷_) (sym (++-assoc Χ₂ C1 N'))))
        ∙ ∙-idr (ap (x' ∷_) (sym (++-assoc Χ₂ C1 N'))) )
    ∙ ∙-invr (ap (x' ∷_) (++-assoc Χ₂ C1 N'))
  sq-G (a ∷ Χ₁) x' Χ₂ C1 N' =
    sq-step-sh (a ∷_)
      (++-assoc (Χ₁ ++ x' ∷ Χ₂) C1 N')
      (++-assoc Χ₁ (x' ∷ Χ₂) (C1 ++ N'))
      (ap (λ l → Χ₁ ++ x' ∷ l) (sym (++-assoc Χ₂ C1 N')))
      (sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) N'))
      (sq-G Χ₁ x' Χ₂ C1 N')

  -- The square behind the outer bridge W of plug-sp's cons case.
  sq-W : ∀ (Χ₁ : List M.Obₘ) (x' : M.Obₘ) (Χ₂ : List M.Obₘ) (Γ₁ Δ : Ctx)
       → sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ)) ⟦ Δ ⟧ᶜ)
         ∙ (sym (ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ⟧ᶜ))
         ∙ (sp-step-path (Χ₁ ++ x' ∷ Χ₂) Γ₁ Δ
         ∙ ++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ++ Δ ⟧ᶜ))
       ≡ ap (λ l → Χ₁ ++ x' ∷ l)
           (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ)))
  sq-W [] x' Χ₂ Γ₁ Δ =
      ∙-idl (refl ∙ (ap (x' ∷_) (sp-step-path Χ₂ Γ₁ Δ) ∙ refl))
    ∙ ∙-idl (ap (x' ∷_) (sp-step-path Χ₂ Γ₁ Δ) ∙ refl)
    ∙ ∙-idr (ap (x' ∷_) (sp-step-path Χ₂ Γ₁ Δ))
    ∙ ap (ap (x' ∷_)) (sq-sp-step Χ₂ Γ₁ Δ)
  sq-W (a ∷ Χ₁) x' Χ₂ Γ₁ Δ =
    sq-stepᵣ₄ (a ∷_)
      (sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ)) ⟦ Δ ⟧ᶜ))
      (sym (ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ⟧ᶜ)))
      (sp-step-path (Χ₁ ++ x' ∷ Χ₂) Γ₁ Δ)
      (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ++ Δ ⟧ᶜ)
      (sq-W Χ₁ x' Χ₂ Γ₁ Δ)

  -- The final square: the head cast of the eval-sp clause against the
  -- statement's boundary (level 2 on Λ' after Χ₁ is gone).
  sq-fin₀ : ∀ (Λ' Χ₂ : List M.Obₘ) (Γ₁ Δ : Ctx)
          → sp-step-path (Λ' ++ Χ₂) Γ₁ Δ ∙ ++-assoc Λ' Χ₂ ⟦ Γ₁ ++ Δ ⟧ᶜ
          ≡ ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc Λ' Χ₂ ⟦ Γ₁ ⟧ᶜ)
            ∙ (++-assoc Λ' (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ) ⟦ Δ ⟧ᶜ
            ∙ ap (λ l → Λ' ++ l)
                (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))))
  sq-fin₀ [] Χ₂ Γ₁ Δ =
      ∙-idr (sp-step-path Χ₂ Γ₁ Δ)
    ∙ sq-sp-step Χ₂ Γ₁ Δ
    ∙ sym ( ∙-idl (refl ∙ (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))))
          ∙ ∙-idl (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))) )
  sq-fin₀ (a ∷ Λ') Χ₂ Γ₁ Δ =
    sq-step₂₃ (a ∷_)
      (sp-step-path (Λ' ++ Χ₂) Γ₁ Δ)
      (++-assoc Λ' Χ₂ ⟦ Γ₁ ++ Δ ⟧ᶜ)
      (ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc Λ' Χ₂ ⟦ Γ₁ ⟧ᶜ))
      (++-assoc Λ' (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ) ⟦ Δ ⟧ᶜ)
      (ap (λ l → Λ' ++ l)
        (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))))
      (sq-fin₀ Λ' Χ₂ Γ₁ Δ)

  sq-fin : ∀ (Χ₁ Λ' Χ₂ : List M.Obₘ) (Γ₁ Δ : Ctx)
         → sp-step-path ((Χ₁ ++ Λ') ++ Χ₂) Γ₁ Δ ∙ sym (nest₂ Χ₁ Λ' Χ₂ ⟦ Γ₁ ++ Δ ⟧ᶜ)
         ≡ ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc (Χ₁ ++ Λ') Χ₂ ⟦ Γ₁ ⟧ᶜ)
           ∙ (sym (nest₂ Χ₁ Λ' (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ) ⟦ Δ ⟧ᶜ)
           ∙ ap (λ l → Χ₁ ++ Λ' ++ l)
               (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))))
  sq-fin [] Λ' Χ₂ Γ₁ Δ = sq-fin₀ Λ' Χ₂ Γ₁ Δ
  sq-fin (a ∷ Χ₁) Λ' Χ₂ Γ₁ Δ =
    sq-step₂₃ (a ∷_)
      (sp-step-path ((Χ₁ ++ Λ') ++ Χ₂) Γ₁ Δ)
      (sym (nest₂ Χ₁ Λ' Χ₂ ⟦ Γ₁ ++ Δ ⟧ᶜ))
      (ap (_++ ⟦ Δ ⟧ᶜ) (++-assoc (Χ₁ ++ Λ') Χ₂ ⟦ Γ₁ ⟧ᶜ))
      (sym (nest₂ Χ₁ Λ' (Χ₂ ++ ⟦ Γ₁ ⟧ᶜ) ⟦ Δ ⟧ᶜ))
      (ap (λ l → Χ₁ ++ Λ' ++ l)
        (++-assoc Χ₂ ⟦ Γ₁ ⟧ᶜ ⟦ Δ ⟧ᶜ ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ))))
      (sq-fin Χ₁ Λ' Χ₂ Γ₁ Δ)

-- ==========================================================================
-- The spine plug lemma: a hom whose exposed slot sits in eval-sp's ambient
-- prefix commutes with the whole spine evaluation — one interchangeₘ per
-- spine entry.  Standalone induction on the spine (not mutual with
-- eval-sub).
-- ==========================================================================

plug-sp : ∀ (Χ₁ : List M.Obₘ) {x' : M.Obₘ} (Χ₂ : List M.Obₘ) {Λ' : List M.Obₘ}
          {As : List G.Ob} {w : M.Obₘ} {Δ : Ctx}
          (h  : M.Homₘ (Χ₁ ++ x' ∷ (Χ₂ ++ map φ.F₀ As)) w)
          (g' : M.Homₘ Λ' x')
          (ts : Sp Δ As)
        → PathP (λ i → M.Homₘ (sym (nest₂ Χ₁ Λ' Χ₂ ⟦ Δ ⟧ᶜ) i) w)
            (eval-sp ((Χ₁ ++ Λ') ++ Χ₂)
              (castₘ (nest₂ Χ₁ Λ' Χ₂ (map φ.F₀ As))
                (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ map φ.F₀ As} h g'))
              ts)
            (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ ⟦ Δ ⟧ᶜ}
              (castₘ (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Δ ⟧ᶜ)
                (eval-sp (Χ₁ ++ x' ∷ Χ₂)
                  (castₘ (sym (++-assoc Χ₁ (x' ∷ Χ₂) (map φ.F₀ As))) h) ts))
              g')
plug-sp Χ₁ {x'} Χ₂ {Λ'} {w = w} h g' [] =
  hom-over (∙-idr (sym (nest₂ Χ₁ Λ' Χ₂ [])))
    (hom-∙P
      (symP (castₘ-filler (nest₂ Χ₁ Λ' Χ₂ [])
        (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ []} h g')))
      (ap (λ k → M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ []} k g')
        (sym (transport⁻transport
          (ap (λ l → M.Homₘ l w) (sym (++-assoc Χ₁ (x' ∷ Χ₂) []))) h))))
plug-sp Χ₁ {x'} Χ₂ {Λ'} {w = w} h g' (_∷_ {Γ = Γ₁} {Δ = Δ'} {As = As'} {A = A} t ts') =
  castₘ-out (sp-step-path Χ Γ₁ Δ')
    (hom-∙P (eval-sp-over (++-assoc (Χ₁ ++ Λ') Χ₂ C1) F ts')
      (hom-∙P (plug-sp Χ₁ (Χ₂ ++ C1) h₂ g' ts') SegC))
    (sq-fin Χ₁ Λ' Χ₂ Γ₁ Δ')
  where
    N' C1 D Χ Y : List M.Obₘ
    N' = map φ.F₀ As'
    C1 = ⟦ Γ₁ ⟧ᶜ
    D  = ⟦ Δ' ⟧ᶜ
    Χ  = (Χ₁ ++ Λ') ++ Χ₂
    Y  = Χ₁ ++ x' ∷ Χ₂

    h̃ : M.Homₘ (Y ++ map φ.F₀ (A ∷ As')) w
    h̃ = castₘ (sym (++-assoc Χ₁ (x' ∷ Χ₂) (map φ.F₀ (A ∷ As')))) h

    ht : M.Homₘ (Y ++ C1 ++ N') w
    ht = M._∘ₘ_ {Θ = Y} {Ξ = N'} h̃ (eval t)

    S₂ : (Y ++ C1 ++ N') ≡ Χ₁ ++ x' ∷ (Χ₂ ++ C1 ++ N')
    S₂ = ++-assoc Χ₁ (x' ∷ Χ₂) (C1 ++ N')

    R : (Y ++ C1 ++ N') ≡ Χ₁ ++ x' ∷ ((Χ₂ ++ C1) ++ N')
    R = S₂ ∙ ap (λ l → Χ₁ ++ x' ∷ l) (sym (++-assoc Χ₂ C1 N'))

    h₂ : M.Homₘ (Χ₁ ++ x' ∷ ((Χ₂ ++ C1) ++ N')) w
    h₂ = castₘ R ht

    Hg : M.Homₘ (Χ ++ map φ.F₀ (A ∷ As')) w
    Hg = castₘ (nest₂ Χ₁ Λ' Χ₂ (map φ.F₀ (A ∷ As')))
           (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ map φ.F₀ (A ∷ As')} h g')

    cvc₁ : PathP (λ i → M.Homₘ (++-assoc Χ₁ Λ' Χ₂ i ++ map φ.F₀ (A ∷ As')) w)
             Hg
             (castₘ (interchange-slot₁ Χ₁ Λ' Χ₂ (φ.F₀ A) N')
               (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ map φ.F₀ (A ∷ As')} h g'))
    cvc₁ = cast-vs-cast
             (nest₂ Χ₁ Λ' Χ₂ (map φ.F₀ (A ∷ As')))
             (interchange-slot₁ Χ₁ Λ' Χ₂ (φ.F₀ A) N')
             (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ map φ.F₀ (A ∷ As')} h g')
             (sq-nest-slot₁ Χ₁ Λ' Χ₂ (φ.F₀ A) N')

    cvc₂ : PathP (λ i → M.Homₘ (Χ₁ ++ x' ∷ sym (++-assoc Χ₂ C1 N') i) w)
             (castₘ S₂ ht) h₂
    cvc₂ = cast-vs-cast S₂ R ht
             (∙-cancell S₂ (ap (λ l → Χ₁ ++ x' ∷ l) (sym (++-assoc Χ₂ C1 N'))))

    F : PathP (λ i → M.Homₘ (ap (_++ N') (++-assoc (Χ₁ ++ Λ') Χ₂ C1) i) w)
          (castₘ (sym (++-assoc Χ C1 N')) (M._∘ₘ_ {Θ = Χ} {Ξ = N'} Hg (eval t)))
          (castₘ (nest₂ Χ₁ Λ' (Χ₂ ++ C1) N')
            (M._∘ₘ_ {Θ = Χ₁} {Ξ = (Χ₂ ++ C1) ++ N'} h₂ g'))
    F = hom-over (sq-F Χ₁ Λ' Χ₂ C1 N')
          (hom-∙P
            (symP (castₘ-filler (sym (++-assoc Χ C1 N'))
              (M._∘ₘ_ {Θ = Χ} {Ξ = N'} Hg (eval t))))
          (hom-∙P
            (λ i → M._∘ₘ_ {Θ = ++-assoc Χ₁ Λ' Χ₂ i} {Ξ = N'} (cvc₁ i) (eval t))
          (hom-∙P
            (M.interchangeₘ {Θ = Χ₁} {Μ = Χ₂} {Κ = N'} {Γ = Λ'} {Δ = C1}
              h g' (eval t))
          (hom-∙P
            (λ i → M._∘ₘ_ {Θ = Χ₁} {Ξ = sym (++-assoc Χ₂ C1 N') i} (cvc₂ i) g')
            (castₘ-filler (nest₂ Χ₁ Λ' (Χ₂ ++ C1) N')
              (M._∘ₘ_ {Θ = Χ₁} {Ξ = (Χ₂ ++ C1) ++ N'} h₂ g'))))))

    Gbr : PathP (λ i → M.Homₘ (++-assoc Χ₁ (x' ∷ Χ₂) C1 i ++ N') w)
          (castₘ (sym (++-assoc Y C1 N')) ht)
          (castₘ (sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) N')) h₂)
    Gbr = hom-over (sq-G Χ₁ x' Χ₂ C1 N')
          (hom-∙P (symP (castₘ-filler (sym (++-assoc Y C1 N')) ht))
          (hom-∙P (castₘ-filler R ht)
            (castₘ-filler (sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) N')) h₂)))

    KIH K0 : M.Homₘ _ w
    KIH = eval-sp (Χ₁ ++ x' ∷ (Χ₂ ++ C1))
            (castₘ (sym (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) N')) h₂) ts'
    K0  = eval-sp (Y ++ C1) (castₘ (sym (++-assoc Y C1 N')) ht) ts'

    W : PathP (λ i → M.Homₘ
                 (Χ₁ ++ x' ∷ (++-assoc Χ₂ C1 D ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ'))) i)
                 w)
          (castₘ (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) D) KIH)
          (castₘ (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ++ Δ' ⟧ᶜ)
            (castₘ (sp-step-path Y Γ₁ Δ') K0))
    W = hom-over (sq-W Χ₁ x' Χ₂ Γ₁ Δ')
          (hom-∙P (symP (castₘ-filler (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) D) KIH))
          (hom-∙P (symP (eval-sp-over (++-assoc Χ₁ (x' ∷ Χ₂) C1) Gbr ts'))
          (hom-∙P (castₘ-filler (sp-step-path Y Γ₁ Δ') K0)
            (castₘ-filler (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ++ Δ' ⟧ᶜ)
              (castₘ (sp-step-path Y Γ₁ Δ') K0)))))

    SegC : PathP (λ i → M.Homₘ
                   (Χ₁ ++ Λ' ++ (++-assoc Χ₂ C1 D ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ'))) i)
                   w)
             (M._∘ₘ_ {Θ = Χ₁} {Ξ = (Χ₂ ++ C1) ++ D}
               (castₘ (++-assoc Χ₁ (x' ∷ (Χ₂ ++ C1)) D) KIH) g')
             (M._∘ₘ_ {Θ = Χ₁} {Ξ = Χ₂ ++ ⟦ Γ₁ ++ Δ' ⟧ᶜ}
               (castₘ (++-assoc Χ₁ (x' ∷ Χ₂) ⟦ Γ₁ ++ Δ' ⟧ᶜ)
                 (castₘ (sp-step-path Y Γ₁ Δ') K0)) g')
    SegC i = M._∘ₘ_ {Θ = Χ₁}
               {Ξ = (++-assoc Χ₂ C1 D ∙ ap (Χ₂ ++_) (sym (⟦⟧-++ Γ₁ Δ'))) i}
               (W i) g'

-- ==========================================================================
-- Glue for the view-dependent squares of the substitution lemma: naturality
-- conjugation, commuting squares with still domain edge, and extending a
-- proved 4-chain square by a trailing segment.
-- ==========================================================================

private
  -- H is a pointwise path between two functions; its value at the far end
  -- of p is the conjugate of its value at the near end.
  conj-nat : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} {f g : X → Y}
             (H : ∀ a → f a ≡ g a) {a₀ a₁ : X} (p : a₀ ≡ a₁)
           → H a₁ ≡ sym (ap f p) ∙ (H a₀ ∙ ap g p)
  conj-nat {f = f} H p =
    sym (flip-cancel (ap f p) (square→commutes (λ k → H (p k))))

  -- A square with still (refl) domain edge commutes: u ∙ L ≡ v.
  square→∙ʳ : ∀ {ℓ} {X : Type ℓ} {a b c : X} {L : b ≡ c} {u : a ≡ b} {v : a ≡ c}
            → PathP (λ k → a ≡ L k) u v → u ∙ L ≡ v
  square→∙ʳ {L = L} {u = u} {v = v} sq =
    sym (square→commutes sq) ∙ ∙-idl v

  -- Extend a proved right-nested 4-chain square by a trailing segment.
  chain4-extend : ∀ {ℓ} {X : Type ℓ} {a b c d e f' : X}
                  (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f')
                  {K : a ≡ e}
                → p ∙ (q ∙ (r ∙ s)) ≡ K
                → p ∙ (q ∙ (r ∙ (s ∙ t))) ≡ K ∙ t
  chain4-extend p q r s t eq =
      ap (λ z' → p ∙ (q ∙ z')) (∙-assoc r s t)
    ∙ ap (p ∙_) (∙-assoc q (r ∙ s) t)
    ∙ ∙-assoc p (q ∙ (r ∙ s)) t
    ∙ ap (_∙ t) eq

-- The eval-sub boundary under an ambient prefix, fully left-nested (the
-- shape plug-sp's prefix argument takes).  Cons-by-cons on Χ, then on Θ.
pre-bound-l : (Χ : List M.Obₘ) (Θ Γ Ξ : Ctx)
            → Χ ++ ⟦ Θ ++ Γ ++ Ξ ⟧ᶜ ≡ ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ) ++ ⟦ Ξ ⟧ᶜ
pre-bound-l (a ∷ Χ) Θ       Γ Ξ = ap (a ∷_) (pre-bound-l Χ Θ Γ Ξ)
pre-bound-l []      (A ∷ Θ) Γ Ξ = ap (⟦ A ⟧ᵗ ∷_) (pre-bound-l [] Θ Γ Ξ)
pre-bound-l []      []      Γ Ξ = ⟦⟧-++ Γ Ξ

-- ==========================================================================
-- Squares for the spine-cons handler (slot in the head).
-- ==========================================================================

private
  -- The bridge from the eval-sp clause's reassociation to plug-sp's LHS.
  sq-cons-L : ∀ (Χ : List M.Obₘ) (Θ Γ Ξ₁ : Ctx) (N₁ : List M.Obₘ)
            → ++-assoc Χ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁
              ∙ (ap (λ l → Χ ++ l ++ N₁) (⟦⟧-++₂ Θ Γ Ξ₁)
              ∙ (sym (assocₘ-boundary Χ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁)
              ∙ nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁))
            ≡ ap (_++ N₁) (pre-bound-l Χ Θ Γ Ξ₁)
  sq-cons-L (a ∷ Χ) Θ Γ Ξ₁ N₁ =
    sq-stepᵣ₄ (a ∷_)
      (++-assoc Χ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁)
      (ap (λ l → Χ ++ l ++ N₁) (⟦⟧-++₂ Θ Γ Ξ₁))
      (sym (assocₘ-boundary Χ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁))
      (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁)
      (sq-cons-L Χ Θ Γ Ξ₁ N₁)
  sq-cons-L [] (A ∷ Θ) Γ Ξ₁ N₁ =
    sq-stepᵣ₄ (⟦ A ⟧ᵗ ∷_)
      (++-assoc [] ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁)
      (ap (λ l → [] ++ l ++ N₁) (⟦⟧-++₂ Θ Γ Ξ₁))
      (sym (assocₘ-boundary [] ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁))
      (nest₂ ([] ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁)
      (sq-cons-L [] Θ Γ Ξ₁ N₁)
  sq-cons-L [] [] Γ Ξ₁ N₁ =
      ∙-idl _
    ∙ ap (ap (λ l → [] ++ l ++ N₁) (⟦⟧-++₂ [] Γ Ξ₁) ∙_)
        (∙-invr (++-assoc ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁))
    ∙ ∙-idr (ap (λ l → [] ++ l ++ N₁) (⟦⟧-++₂ [] Γ Ξ₁))

  -- The bridge from the head-slot substitution (after the IH) to plug-sp's
  -- slot-exposed hom: generic in the interpreted slot path pS.
  sq-slotE : ∀ (Χ : List M.Obₘ) {L T X' : List M.Obₘ} {x' : M.Obₘ}
             (pS : L ≡ T ++ x' ∷ X') (N₁ : List M.Obₘ)
           → ++-assoc Χ L N₁
             ∙ (ap (λ l → Χ ++ l ++ N₁) pS
             ∙ (slot-unbury Χ T x' X' N₁
             ∙ sym (++-assoc (Χ ++ T) (x' ∷ X') N₁)))
           ≡ ap (_++ N₁) (pre-split Χ pS)
  sq-slotE [] {T = T} {X' = X'} {x' = x'} pS N₁ =
      ∙-idl _
    ∙ ap (ap (λ l → [] ++ l ++ N₁) pS ∙_)
        (∙-invr (++-assoc T (x' ∷ X') N₁))
    ∙ ∙-idr (ap (λ l → [] ++ l ++ N₁) pS)
  sq-slotE (a ∷ Χ) {T = T} {X' = X'} {x' = x'} pS N₁ =
    sq-stepᵣ₄ (a ∷_)
      (++-assoc Χ _ N₁)
      (ap (λ l → Χ ++ l ++ N₁) pS)
      (slot-unbury Χ T x' X' N₁)
      (sym (++-assoc (Χ ++ T) (x' ∷ X') N₁))
      (sq-slotE Χ pS N₁)

  -- The outer bridge square of the spine-cons handler: the canonical
  -- weakened split against the clause's head cast.  Χ first, then the
  -- split itself.
  sq-WEcore : ∀ (Χ : List M.Obₘ) {x : Ty} {Θ Γ₁ Ξ₁ : Ctx}
              (s₁ : Split x Θ Γ₁ Ξ₁) (Δ₁ : Ctx)
            → sym (++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ Δ₁ ⟧ᶜ)
              ∙ (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split Χ (⟦split⟧ s₁)))
              ∙ (sp-step-path Χ Γ₁ Δ₁
              ∙ pre-split Χ (⟦split⟧ (split-++ˡ s₁ Δ₁))))
            ≡ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δ₁))
  sq-WEcore (a ∷ Χ) {x = x} {Θ = Θ} {Ξ₁ = Ξ₁} s₁ Δ₁ =
    sq-stepᵣ₄ (a ∷_)
      (sym (++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ Δ₁ ⟧ᶜ))
      (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split Χ (⟦split⟧ s₁))))
      (sp-step-path Χ _ Δ₁)
      (pre-split Χ (⟦split⟧ (split-++ˡ s₁ Δ₁)))
      (sq-WEcore Χ s₁ Δ₁)
  sq-WEcore [] {x = x} {Ξ₁ = Ξ₁} here Δ₁ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ∙-idr (sym (⟦⟧-++ (x ∷ Ξ₁) Δ₁))
  sq-WEcore [] {x = x} {Ξ₁ = Ξ₁} (there {a = A'} s₁') Δ₁ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (++-assoc ([] ++ ⟦ _ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ Δ₁ ⟧ᶜ))
      (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split [] (⟦split⟧ s₁'))))
      (sp-step-path [] _ Δ₁)
      (pre-split [] (⟦split⟧ (split-++ˡ s₁' Δ₁)))
      (sq-WEcore [] s₁' Δ₁)

  -- Extend at depth 5 and conjugate: pure groupoid algebra shared by the
  -- total squares of the handlers.
  chain5-shift : ∀ {ℓ} {X : Type ℓ} {a b c d e f' g' : X}
                 (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f')
                 (c' : f' ≡ g')
               → p ∙ (q ∙ (r ∙ (s ∙ (t ∙ c'))))
               ≡ (p ∙ (q ∙ (r ∙ (s ∙ t)))) ∙ c'
  chain5-shift p q r s t c' =
      ap (λ z' → p ∙ (q ∙ (r ∙ z'))) (∙-assoc s t c')
    ∙ ap (λ z' → p ∙ (q ∙ z')) (∙-assoc r (s ∙ t) c')
    ∙ ap (p ∙_) (∙-assoc q (r ∙ (s ∙ t)) c')
    ∙ ∙-assoc p (q ∙ (r ∙ (s ∙ t))) c'

  chain-conj : ∀ {ℓ} {X : Type ℓ} {a₀ a b c d e f' g' : X}
               (d' : a₀ ≡ a)
               (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f')
               (c' : f' ≡ g')
             → (d' ∙ p) ∙ (q ∙ (r ∙ (s ∙ (t ∙ c'))))
             ≡ d' ∙ ((p ∙ (q ∙ (r ∙ (s ∙ t)))) ∙ c')
  chain-conj d' p q r s t c' =
      sym (∙-assoc d' p (q ∙ (r ∙ (s ∙ (t ∙ c')))))
    ∙ ap (d' ∙_) (chain5-shift p q r s t c')

  -- The p-free core of the spine-cons-left total square (Χ, then Θ, then Γ;
  -- the Ξ₁ level is uniform).
  sq-total-L₀ : ∀ (Χ : List M.Obₘ) (Θ Γ Ξ₁ Δ₁ : Ctx)
    → sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁))
      ∙ (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁)
      ∙ (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁)
      ∙ (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ)
      ∙ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)))))
    ≡ pre-bound Χ Θ Γ (Ξ₁ ++ Δ₁)
  sq-total-L₀ (a ∷ Χ) Θ Γ Ξ₁ Δ₁ =
    sq-stepᵣ₅ (a ∷_)
      (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁)))
      (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁))
      (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁))
      (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ))
      (ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)))
      (sq-total-L₀ Χ Θ Γ Ξ₁ Δ₁)
  sq-total-L₀ [] (A ∷ Θ) Γ Ξ₁ Δ₁ =
    sq-stepᵣ₅ (⟦ A ⟧ᵗ ∷_)
      (sym (ap (λ l → [] ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁)))
      (sym (sp-step-path [] (Θ ++ Γ ++ Ξ₁) Δ₁))
      (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l [] Θ Γ Ξ₁))
      (sym (nest₂ ([] ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ))
      (ap (λ l → ([] ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)))
      (sq-total-L₀ [] Θ Γ Ξ₁ Δ₁)
  sq-total-L₀ [] [] (B ∷ Γ) Ξ₁ Δ₁ =
    sq-stepᵣ₅ (⟦ B ⟧ᵗ ∷_)
      (sym (ap (λ l → [] ++ ⟦ l ⟧ᶜ) (flattenˡ [] Γ Ξ₁ Δ₁)))
      (sym (sp-step-path [] ([] ++ Γ ++ Ξ₁) Δ₁))
      (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l [] [] Γ Ξ₁))
      (sym (nest₂ ([] ++ ⟦ [] ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ))
      (ap (λ l → ([] ++ ⟦ [] ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)))
      (sq-total-L₀ [] [] Γ Ξ₁ Δ₁)
  sq-total-L₀ [] [] [] Ξ₁ Δ₁ =
      ∙-idl _
    ∙ ap (⟦⟧-++ Ξ₁ Δ₁ ∙_) (∙-idl _ ∙ ∙-idl _)
    ∙ ∙-invr (⟦⟧-++ Ξ₁ Δ₁)

-- ==========================================================================
-- Spine-cons handler, slot in the head: peel the handler cast, rewrite the
-- head by the substitution IH under f, reassociate (assocₘ), run plug-sp,
-- and land on the clause's canonical form via the view's soundness square.
-- ==========================================================================

core-cons-left : ∀ (Χ : List M.Obₘ) {A : G.Ob} {As' : List G.Ob} {w : M.Obₘ}
    (f : M.Homₘ (Χ ++ map φ.F₀ (A ∷ As')) w)
    {x : Ty} {Θ Γ₁ Ξ₁ Δ₁ Ξ Γ : Ctx}
    (s₁ : Split x Θ Γ₁ Ξ₁) (p : Ξ₁ ++ Δ₁ ≡ Ξ)
    {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (co : PathP (λ k → Split x Θ (Γ₁ ++ Δ₁) (p k)) (split-++ˡ s₁ Δ₁) s)
    (t : Tm Γ₁ (base A)) (ts₁ : Sp Δ₁ As') (g : Tm Γ x)
    (IHt : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ₁ i) (φ.F₀ A))
             (eval (sub s₁ t g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ}
               (castₘ (⟦split⟧ s₁) (eval t)) (eval g)))
  → PathP (λ i → M.Homₘ (pre-bound Χ Θ Γ Ξ i) w)
      (eval-sp Χ f (sub-cons (on-left s₁ p co) t ts₁ g))
      (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f (t ∷ ts₁))) (eval g))
core-cons-left Χ {A} {As'} {w} f {x} {Θ} {Γ₁} {Ξ₁} {Δ₁} {Ξ} {Γ} s₁ p {s} co t ts₁ g IHt =
  hom-over sq-tot
    (hom-∙P (symP (eval-sp-cast Χ f Cp (sub s₁ t g ∷ ts₁)))
    (hom-∙P (symP (castₘ-filler (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁) L1))
    (hom-∙P (eval-sp-over (pre-bound-l Χ Θ Γ Ξ₁) FL ts₁)
    (hom-∙P (plug-sp (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Ξ₁ ⟧ᶜ hP (eval g) ts₁)
            SegE))))
  where
    N₁ : List M.Obₘ
    N₁ = map φ.F₀ As'

    Cp : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ Ξ
    Cp = flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p

    u₁ : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (φ.F₀ A)
    u₁ = castₘ (⟦split⟧ s₁) (eval t)

    hP : M.Homₘ ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ N₁)) w
    hP = castₘ (slot-unbury Χ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ N₁)
           (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f u₁)

    L1 : M.Homₘ ((Χ ++ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ) w
    L1 = eval-sp (Χ ++ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ)
           (castₘ (sym (++-assoc Χ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁))
             (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval (sub s₁ t g))))
           ts₁

    FL : PathP (λ i → M.Homₘ (ap (_++ N₁) (pre-bound-l Χ Θ Γ Ξ₁) i) w)
           (castₘ (sym (++-assoc Χ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁))
             (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval (sub s₁ t g))))
           (castₘ (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁)
             (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ N₁} hP (eval g)))
    FL = hom-over (sq-cons-L Χ Θ Γ Ξ₁ N₁)
           (hom-∙P (symP (castₘ-filler (sym (++-assoc Χ ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ N₁))
                      (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval (sub s₁ t g)))))
           (hom-∙P (λ i → M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (IHt i))
           (hom-∙P (symP (M.assocₘ {Θ = Χ} {Ξ = N₁} {Φ = ⟦ Θ ⟧ᶜ} {Ψ = ⟦ Ξ₁ ⟧ᶜ}
                            {Ρ = ⟦ Γ ⟧ᶜ} f u₁ (eval g)))
                   (castₘ-filler (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ N₁)
                     (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ N₁} hP (eval g))))))

    KIH' : M.Homₘ (((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ) w
    KIH' = eval-sp ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ)
             (castₘ (sym (++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) N₁)) hP) ts₁

    K1 : M.Homₘ ((Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ) w
    K1 = eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ)
           (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ N₁))
             (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval t))) ts₁

    FE : PathP (λ i → M.Homₘ (ap (_++ N₁) (pre-split Χ (⟦split⟧ s₁)) i) w)
           (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ N₁))
             (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval t)))
           (castₘ (sym (++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) N₁)) hP)
    FE = hom-over (sq-slotE Χ (⟦split⟧ s₁) N₁)
           (hom-∙P (symP (castₘ-filler (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ N₁))
                      (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval t))))
           (hom-∙P (λ i → M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f
                            (castₘ-filler (⟦split⟧ s₁) (eval t) i))
           (hom-∙P (castₘ-filler (slot-unbury Χ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ N₁)
                      (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f u₁))
                   (castₘ-filler (sym (++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) N₁)) hP))))

    ΞE : (⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ) ≡ ⟦ Ξ ⟧ᶜ
    ΞE = sym (⟦⟧-++ Ξ₁ Δ₁) ∙ ap ⟦_⟧ᶜ p

    pB : ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ
       ≡ (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ)
    pB = ++-assoc (Χ ++ ⟦ Θ ⟧ᶜ) (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ Δ₁ ⟧ᶜ

    sq-WE : sym pB
            ∙ (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split Χ (⟦split⟧ s₁)))
            ∙ (sp-step-path Χ Γ₁ Δ₁ ∙ pre-split Χ (⟦split⟧ s)))
          ≡ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) ΞE
    sq-WE =
        ap (λ w' → sym pB ∙ (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split Χ (⟦split⟧ s₁)))
                     ∙ (sp-step-path Χ Γ₁ Δ₁ ∙ w')))
           (sym (square→∙ʳ (λ k → pre-split Χ (⟦split⟧ (co k)))))
      ∙ chain4-extend (sym pB)
          (sym (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-split Χ (⟦split⟧ s₁))))
          (sp-step-path Χ Γ₁ Δ₁)
          (pre-split Χ (⟦split⟧ (split-++ˡ s₁ Δ₁)))
          (ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (ap ⟦_⟧ᶜ p))
          (sq-WEcore Χ s₁ Δ₁)
      ∙ ∙-ap₂' (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δ₁)) (ap ⟦_⟧ᶜ p)

    WE : PathP (λ i → M.Homₘ ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ΞE i) w)
           (castₘ pB KIH')
           (castₘ (pre-split Χ (⟦split⟧ s)) (castₘ (sp-step-path Χ Γ₁ Δ₁) K1))
    WE = hom-over sq-WE
           (hom-∙P (symP (castₘ-filler pB KIH'))
           (hom-∙P (symP (eval-sp-over (pre-split Χ (⟦split⟧ s₁)) FE ts₁))
           (hom-∙P (castₘ-filler (sp-step-path Χ Γ₁ Δ₁) K1)
                   (castₘ-filler (pre-split Χ (⟦split⟧ s))
                     (castₘ (sp-step-path Χ Γ₁ Δ₁) K1)))))

    SegE : PathP (λ i → M.Homₘ ((Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ ΞE i) w)
             (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ}
               (castₘ pB KIH') (eval g))
             (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f (t ∷ ts₁))) (eval g))
    SegE i = M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ΞE i} (WE i) (eval g)

    sq-tot : sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) Cp)
             ∙ (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁)
             ∙ (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁)
             ∙ (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ)
             ∙ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) ΞE)))
           ≡ pre-bound Χ Θ Γ Ξ
    sq-tot =
        ap (_∙ (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁)
               ∙ (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁)
               ∙ (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ)
               ∙ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) ΞE))))
           (ap sym (ap-∙ (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁)
                      (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
            ∙ sym-∙ (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁))
                    (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
      ∙ ap (λ v' → (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                    ∙ sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁)))
                   ∙ (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁)
                   ∙ (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁)
                   ∙ (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ) ∙ v'))))
           (ap-∙ (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)) (ap ⟦_⟧ᶜ p))
      ∙ chain-conj (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
          (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenˡ Θ Γ Ξ₁ Δ₁)))
          (sym (sp-step-path Χ (Θ ++ Γ ++ Ξ₁) Δ₁))
          (ap (_++ ⟦ Δ₁ ⟧ᶜ) (pre-bound-l Χ Θ Γ Ξ₁))
          (sym (nest₂ (Χ ++ ⟦ Θ ⟧ᶜ) ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ))
          (ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δ₁)))
          (ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p))
      ∙ ap (λ K → sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                  ∙ (K ∙ ap (λ l → (Χ ++ ⟦ Θ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)))
           (sq-total-L₀ Χ Θ Γ Ξ₁ Δ₁)
      ∙ sym (conj-nat (pre-bound Χ Θ Γ) p)

-- ==========================================================================
-- Squares for the spine-cons handler, slot in the tail.
-- ==========================================================================

private
  chain3-extend : ∀ {ℓ} {X : Type ℓ} {a b c d e : X}
                  (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (t : d ≡ e) {K : a ≡ d}
                → p ∙ (q ∙ r) ≡ K
                → p ∙ (q ∙ (r ∙ t)) ≡ K ∙ t
  chain3-extend p q r t eq =
    ap (p ∙_) (∙-assoc q r t) ∙ ∙-assoc p (q ∙ r) t ∙ ap (_∙ t) eq

  -- Two-sided cons step: LHS a right-nested 3-chain, RHS a 2-chain.
  sq-step₃₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : a ≡ e) (t : e ≡ d)
            → p ∙ (q ∙ r) ≡ s ∙ t
            → ap f p ∙ (ap f q ∙ ap f r) ≡ ap f s ∙ ap f t
  sq-step₃₂ f p q r s t eq =
    ∙-ap₃ f p q r ∙ ap (ap f) eq ∙ sym (∙-ap₂' f s t)

  -- The canonical prefix-weakened split against the clause's head cast.
  sq-WRcore : ∀ (Χ : List M.Obₘ) {x : Ty} {Θ₂ Δ₁ Ξ : Ctx} (Γ₁ : Ctx)
              (s₂ : Split x Θ₂ Δ₁ Ξ)
            → sym (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂))
              ∙ (sp-step-path Χ Γ₁ Δ₁
              ∙ pre-split Χ (⟦split⟧ (split-++ʳ Γ₁ s₂)))
            ≡ ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ)
              ∙ ap (λ l → (Χ ++ l) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂))
  sq-WRcore (a ∷ Χ) {x = x} {Θ₂ = Θ₂} {Ξ = Ξ} Γ₁ s₂ =
    sq-step₃₂ (a ∷_)
      (sym (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)))
      (sp-step-path Χ Γ₁ _)
      (pre-split Χ (⟦split⟧ (split-++ʳ Γ₁ s₂)))
      (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
      (ap (λ l → (Χ ++ l) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
      (sq-WRcore Χ Γ₁ s₂)
  sq-WRcore [] {x = x} {Θ₂ = Θ₂} {Ξ = Ξ} (A ∷ Γ₁) s₂ =
    sq-step₃₂ (⟦ A ⟧ᵗ ∷_)
      (sym (pre-split ([] ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)))
      (sp-step-path [] Γ₁ _)
      (pre-split [] (⟦split⟧ (split-++ʳ Γ₁ s₂)))
      (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc [] ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
      (ap (λ l → ([] ++ l) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
      (sq-WRcore [] Γ₁ s₂)
  sq-WRcore [] [] s₂ =
      ap (sym (⟦split⟧ s₂) ∙_) (∙-idl (⟦split⟧ s₂))
    ∙ ∙-invl (⟦split⟧ s₂)
    ∙ sym (∙-idl refl)

  -- The p-free core of the spine-cons-right total square.
  sq-tot-R₀ : ∀ (Χ : List M.Obₘ) (Γ₁ Θ₂ Γ Ξ : Ctx)
    → sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ))
      ∙ (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ))
      ∙ (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ
      ∙ (ap (_++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ)
      ∙ ap (λ l → (Χ ++ l) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))))
    ≡ pre-bound Χ (Γ₁ ++ Θ₂) Γ Ξ
  sq-tot-R₀ (a ∷ Χ) Γ₁ Θ₂ Γ Ξ =
    sq-stepᵣ₅ (a ∷_)
      (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ)))
      (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ)))
      (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ)
      (ap (_++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
      (ap (λ l → (Χ ++ l) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
      (sq-tot-R₀ Χ Γ₁ Θ₂ Γ Ξ)
  sq-tot-R₀ [] (A ∷ Γ₁) Θ₂ Γ Ξ =
    sq-stepᵣ₅ (⟦ A ⟧ᵗ ∷_)
      (sym (ap (λ l → [] ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ)))
      (sym (sp-step-path [] Γ₁ (Θ₂ ++ Γ ++ Ξ)))
      (pre-bound ([] ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ)
      (ap (_++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc [] ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
      (ap (λ l → ([] ++ l) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
      (sq-tot-R₀ [] Γ₁ Θ₂ Γ Ξ)
  sq-tot-R₀ [] [] Θ₂ Γ Ξ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ap (⟦⟧-++₂ Θ₂ Γ Ξ ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦⟧-++₂ Θ₂ Γ Ξ)

-- ==========================================================================
-- Spine-cons handler, slot in the tail: peel the handler cast, evaluate the
-- head as in the clause, recurse (IHsp), and reconcile prefixes via the
-- view's soundness square.
-- ==========================================================================

core-cons-right : ∀ (Χ : List M.Obₘ) {A : G.Ob} {As' : List G.Ob} {w : M.Obₘ}
    (f : M.Homₘ (Χ ++ map φ.F₀ (A ∷ As')) w)
    {x : Ty} {Γ₁ Δ₁ Θ₂ Ξ Θ Γ : Ctx}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (co : PathP (λ k → Split x (q k) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₂) s)
    (t : Tm Γ₁ (base A)) (ts₁ : Sp Δ₁ As') (g : Tm Γ x)
    (IHsp : PathP (λ i → M.Homₘ (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ i) w)
              (eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ)
                (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ As')))
                  (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ As'} f (eval t)))
                (sub-sp s₂ ts₁ g))
              (M._∘ₘ_ {Θ = (Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                (castₘ (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂))
                  (eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ)
                    (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ As')))
                      (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ As'} f (eval t)))
                    ts₁))
                (eval g)))
  → PathP (λ i → M.Homₘ (pre-bound Χ Θ Γ Ξ i) w)
      (eval-sp Χ f (sub-cons (on-right s₂ q co) t ts₁ g))
      (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f (t ∷ ts₁))) (eval g))
core-cons-right Χ {A} {As'} {w} f {x} {Γ₁} {Δ₁} {Θ₂} {Ξ} {Θ} {Γ} s₂ q {s} co t ts₁ g IHsp =
  hom-over sq-tot
    (hom-∙P (symP (eval-sp-cast Χ f CR (t ∷ sub-sp s₂ ts₁ g)))
    (hom-∙P (symP (castₘ-filler (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ)) LR))
    (hom-∙P IHsp SegR)))
  where
    N₁ : List M.Obₘ
    N₁ = map φ.F₀ As'

    CR : Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ Θ ++ Γ ++ Ξ
    CR = flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q

    fh : M.Homₘ ((Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ N₁) w
    fh = castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ N₁))
           (M._∘ₘ_ {Θ = Χ} {Ξ = N₁} f (eval t))

    LR : M.Homₘ ((Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Θ₂ ++ Γ ++ Ξ ⟧ᶜ) w
    LR = eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ) fh (sub-sp s₂ ts₁ g)

    K1 : M.Homₘ ((Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ) w
    K1 = eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ) fh ts₁

    ΘE : ⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    ΘE = sym (⟦⟧-++ Γ₁ Θ₂) ∙ ap ⟦_⟧ᶜ q

    ΘR : (Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Θ₂ ⟧ᶜ ≡ Χ ++ ⟦ Θ ⟧ᶜ
    ΘR = ++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ∙ ap (Χ ++_) ΘE

    sq-WR : sym (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂))
            ∙ (sp-step-path Χ Γ₁ Δ₁ ∙ pre-split Χ (⟦split⟧ s))
          ≡ ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ΘR
    sq-WR =
        ap (λ w' → sym (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂))
                   ∙ (sp-step-path Χ Γ₁ Δ₁ ∙ w'))
           (sym (square→∙ʳ (λ k → pre-split Χ (⟦split⟧ (co k)))))
      ∙ chain3-extend
          (sym (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)))
          (sp-step-path Χ Γ₁ Δ₁)
          (pre-split Χ (⟦split⟧ (split-++ʳ Γ₁ s₂)))
          (ap (λ l → (Χ ++ ⟦ l ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q)
          (sq-WRcore Χ Γ₁ s₂)
      ∙ sym (∙-assoc (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
                     (ap (λ l → (Χ ++ l) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
                     (ap (λ l → (Χ ++ ⟦ l ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q))
      ∙ ap (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ) ∙_)
           (∙-ap₂' (λ l → (Χ ++ l) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)) (ap ⟦_⟧ᶜ q))
      ∙ ∙-ap₂' (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ) (ap (Χ ++_) ΘE)

    WR : PathP (λ k → M.Homₘ (ΘR k ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) w)
           (castₘ (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)) K1)
           (castₘ (pre-split Χ (⟦split⟧ s)) (castₘ (sp-step-path Χ Γ₁ Δ₁) K1))
    WR = hom-over sq-WR
           (hom-∙P (symP (castₘ-filler (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)) K1))
           (hom-∙P (castₘ-filler (sp-step-path Χ Γ₁ Δ₁) K1)
                   (castₘ-filler (pre-split Χ (⟦split⟧ s))
                     (castₘ (sp-step-path Χ Γ₁ Δ₁) K1))))

    SegR : PathP (λ k → M.Homₘ (ΘR k ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) w)
             (M._∘ₘ_ {Θ = (Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (pre-split (Χ ++ ⟦ Γ₁ ⟧ᶜ) (⟦split⟧ s₂)) K1) (eval g))
             (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f (t ∷ ts₁))) (eval g))
    SegR k = M._∘ₘ_ {Θ = ΘR k} {Ξ = ⟦ Ξ ⟧ᶜ} (WR k) (eval g)

    sq-tot : sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) CR)
             ∙ (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ))
             ∙ (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ
             ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘR))
           ≡ pre-bound Χ Θ Γ Ξ
    sq-tot =
        ap (_∙ (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ))
               ∙ (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ
               ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘR)))
           (ap sym (ap-∙ (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ)
                      (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
            ∙ sym-∙ (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ))
                    (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)))
      ∙ ap (λ v' → (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
                    ∙ sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ)))
                   ∙ (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ))
                   ∙ (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ ∙ v')))
           (ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ) (ap (Χ ++_) ΘE)
            ∙ ap (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ) ∙_)
                 (ap-∙ (λ l → (Χ ++ l) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)) (ap ⟦_⟧ᶜ q)))
      ∙ chain-conj (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)))
          (sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (flattenʳ Γ₁ Θ₂ Γ Ξ)))
          (sym (sp-step-path Χ Γ₁ (Θ₂ ++ Γ ++ Ξ)))
          (pre-bound (Χ ++ ⟦ Γ₁ ⟧ᶜ) Θ₂ Γ Ξ)
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (++-assoc Χ ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ))
          (ap (λ l → (Χ ++ l) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
          (ap (λ l → (Χ ++ ⟦ l ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q)
      ∙ ap (λ K → sym (ap (λ l → Χ ++ ⟦ l ⟧ᶜ) (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
                  ∙ (K ∙ ap (λ l → (Χ ++ ⟦ l ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
           (sq-tot-R₀ Χ Γ₁ Θ₂ Γ Ξ)
      ∙ sym (conj-nat (λ Θ' → pre-bound Χ Θ' Γ Ξ) q)

-- ==========================================================================
-- Squares for the pair handler, slot in the left component.
-- ==========================================================================

private
  -- assocₘ's boundary at Θ = [] with singleton-tailed suffix is
  -- interchange-slot₁ (both cons-by-cons with the same base).
  sq-flatten-slot₁ : ∀ (T C X : List M.Obₘ) (b : M.Obₘ)
                   → assocₘ-flatten T C X (b ∷ []) ≡ interchange-slot₁ T C X b []
  sq-flatten-slot₁ []      C X b = refl
  sq-flatten-slot₁ (a ∷ T) C X b = ap (ap (a ∷_)) (sq-flatten-slot₁ T C X b)

  -- The outer-bridge core square of the pair-left handler (induction on the
  -- split; the ambient prefix is the split's own Θ).
  sq-pair-Wcore : ∀ {x : Ty} {Θ Γ₁ Ξ₁ : Ctx} (s₁ : Split x Θ Γ₁ Ξ₁) (Δ₁ : Ctx)
                → sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ Δ₁ ⟧ᶜ ++ []))
                  ∙ (sym (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦split⟧ s₁))
                  ∙ (pair-path Γ₁ Δ₁ ∙ ⟦split⟧ (split-++ˡ s₁ Δ₁)))
                ≡ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (pair-path Ξ₁ Δ₁)
  sq-pair-Wcore {x = x} {Ξ₁ = Ξ₁} here Δ₁ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ∙-idr (ap (⟦ x ⟧ᵗ ∷_) (pair-path Ξ₁ Δ₁))
  sq-pair-Wcore {x = x} {Ξ₁ = Ξ₁} (there {a = A'} s₁') Δ₁ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (++-assoc ⟦ _ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ Δ₁ ⟧ᶜ ++ [])))
      (sym (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦split⟧ s₁')))
      (pair-path _ Δ₁)
      (⟦split⟧ (split-++ˡ s₁' Δ₁))
      (sq-pair-Wcore s₁' Δ₁)

  -- The p-free core of the pair-left total square (Θ then Γ).
  sq-tot-pair₀ : ∀ (Θ Γ Ξ₁ Δ₁ : Ctx)
    → sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁))
      ∙ (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁)
      ∙ (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁)
      ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ []
      ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (pair-path Ξ₁ Δ₁))))
    ≡ ⟦⟧-++₂ Θ Γ (Ξ₁ ++ Δ₁)
  sq-tot-pair₀ (A ∷ Θ) Γ Ξ₁ Δ₁ =
    sq-stepᵣ₅ (⟦ A ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁)))
      (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁))
      (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁))
      (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [])
      (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (pair-path Ξ₁ Δ₁))
      (sq-tot-pair₀ Θ Γ Ξ₁ Δ₁)
  sq-tot-pair₀ [] (B ∷ Γ) Ξ₁ Δ₁ =
    sq-stepᵣ₅ (⟦ B ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenˡ [] Γ Ξ₁ Δ₁)))
      (sym (pair-path (Γ ++ Ξ₁) Δ₁))
      (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ [] Γ Ξ₁))
      (interchangeₘ-boundary ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [])
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (pair-path Ξ₁ Δ₁))
      (sq-tot-pair₀ [] Γ Ξ₁ Δ₁)
  sq-tot-pair₀ [] [] Ξ₁ Δ₁ =
      ∙-idl _
    ∙ ap (sym (pair-path Ξ₁ Δ₁) ∙_) (∙-idl _ ∙ ∙-idl _)
    ∙ ∙-invl (pair-path Ξ₁ Δ₁)

-- ==========================================================================
-- Pair handler, slot in the left component: rewrite by the IH under the
-- binary universal arrow, reassociate (assocₘ, homogeneous via from-pathp),
-- interchange the g- and Q-pluggings, and land via the view's soundness
-- square.
-- ==========================================================================

core-pair-left : ∀ {x A B : Ty} {Θ Γ₁ Ξ₁ Δ₁ Ξ Γ : Ctx}
    (s₁ : Split x Θ Γ₁ Ξ₁) (p : Ξ₁ ++ Δ₁ ≡ Ξ)
    {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (co : PathP (λ k → Split x Θ (Γ₁ ++ Δ₁) (p k)) (split-++ˡ s₁ Δ₁) s)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x)
    (IHP : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ₁ i) ⟦ A ⟧ᵗ)
             (eval (sub s₁ P g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ} (castₘ (⟦split⟧ s₁) (eval P)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ A ⊗ B ⟧ᵗ)
      (eval (sub-pair (on-left s₁ p co) P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval ⦅ P , Q ⦆)) (eval g))
core-pair-left {x} {A} {B} {Θ} {Γ₁} {Ξ₁} {Δ₁} {Ξ} {Γ} s₁ p {s} co P Q g IHP =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast Cp ⦅ sub s₁ P g , Q ⦆))
    (hom-∙P (symP (castₘ-filler (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁) inner0))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦⟧-++₂ Θ Γ Ξ₁ i} {Ξ = []}
               (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ (IHP i)) (eval Q))
    (hom-∙P (homog ◁ Ic) SegP))))
  where
    u₂ : M.Homₘ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ A ⊗ B ⟧ᵗ
    u₂ = uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])

    u₁' : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ A ⟧ᵗ
    u₁' = castₘ (⟦split⟧ s₁) (eval P)

    E₂ : List M.Obₘ
    E₂ = ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ

    Cp : (Θ ++ Γ ++ Ξ₁) ++ Δ₁ ≡ Θ ++ Γ ++ Ξ
    Cp = flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p

    inner0 : M.Homₘ (⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ []) ⟦ A ⊗ B ⟧ᵗ
    inner0 = M._∘ₘ_ {Θ = ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ} {Ξ = []}
               (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ (eval (sub s₁ P g))) (eval Q)

    W : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ [])) ⟦ A ⊗ B ⟧ᵗ
    W = castₘ (slot-unbury [] ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ []))
          (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ u₁')

    S₀' : ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ []
        ≡ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⟦ B ⟧ᵗ ∷ []
    S₀' = interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ B ⟧ᵗ []

    S₁' : ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ [] ≡ E₂ ++ ⟦ B ⟧ᵗ ∷ []
    S₁' = interchange-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ B ⟧ᵗ []

    S₂' : (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⟦ Δ₁ ⟧ᶜ ++ []
        ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ [])
    S₂' = interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ []

    homog : M._∘ₘ_ {Θ = E₂} {Ξ = []}
              (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ} u₁' (eval g))) (eval Q)
          ≡ M._∘ₘ_ {Θ = E₂} {Ξ = []}
              (castₘ S₁'
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ []} W (eval g))) (eval Q)
    homog = ap (λ k → M._∘ₘ_ {Θ = E₂} {Ξ = []} k (eval Q))
              ( sym (from-pathp (M.assocₘ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} {Φ = ⟦ Θ ⟧ᶜ}
                       {Ψ = ⟦ Ξ₁ ⟧ᶜ} {Ρ = ⟦ Γ ⟧ᶜ} u₂ u₁' (eval g)))
              ∙ cast-vs-cast (assocₘ-boundary [] ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ [])) S₁'
                  (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ []} W (eval g))
                  ( ap (λ z' → sym z' ∙ S₁')
                       (sq-flatten-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ B ⟧ᵗ)
                  ∙ ∙-invl S₁' ))

    Ic : PathP (λ i → M.Homₘ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [] i)
                       ⟦ A ⊗ B ⟧ᵗ)
          (M._∘ₘ_ {Θ = E₂} {Ξ = []}
            (castₘ S₁' (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ []} W (eval g)))
            (eval Q))
          (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ []}
            (castₘ S₂'
              (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = []} (castₘ S₀' W) (eval Q)))
            (eval g))
    Ic = M.interchangeₘ {Θ = ⟦ Θ ⟧ᶜ} {Μ = ⟦ Ξ₁ ⟧ᶜ} {Κ = []} {Γ = ⟦ Γ ⟧ᶜ} {Δ = ⟦ Δ₁ ⟧ᶜ}
          W (eval g) (eval Q)

    PQ : M.Homₘ (⟦ Γ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ []) ⟦ A ⊗ B ⟧ᵗ
    PQ = M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []}
           (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ (eval P)) (eval Q)

    Z : PathP (λ k → M.Homₘ (⟦split⟧ s₁ k ++ ⟦ B ⟧ᵗ ∷ []) ⟦ A ⊗ B ⟧ᵗ)
          (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ (eval P))
          (castₘ S₀' W)
    Z = hom-over
          ( ap (ap (λ l → l ++ ⟦ B ⟧ᵗ ∷ []) (⟦split⟧ s₁) ∙_)
               (∙-invr (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ B ⟧ᵗ ∷ [])))
          ∙ ∙-idr (ap (λ l → l ++ ⟦ B ⟧ᵗ ∷ []) (⟦split⟧ s₁)) )
          (hom-∙P (λ i → M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂
                           (castₘ-filler (⟦split⟧ s₁) (eval P) i))
          (hom-∙P (castₘ-filler (slot-unbury [] ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ []))
                     (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ u₁'))
                  (castₘ-filler S₀' W)))

    ΞP : ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ [] ≡ ⟦ Ξ ⟧ᶜ
    ΞP = pair-path Ξ₁ Δ₁ ∙ ap ⟦_⟧ᶜ p

    sq-pair-W : sym S₂'
                ∙ (sym (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦split⟧ s₁))
                ∙ (pair-path Γ₁ Δ₁ ∙ ⟦split⟧ s))
              ≡ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) ΞP
    sq-pair-W =
        ap (λ w' → sym S₂' ∙ (sym (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦split⟧ s₁))
                     ∙ (pair-path Γ₁ Δ₁ ∙ w')))
           (sym (square→∙ʳ (λ k → ⟦split⟧ (co k))))
      ∙ chain4-extend (sym S₂')
          (sym (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦split⟧ s₁)))
          (pair-path Γ₁ Δ₁)
          (⟦split⟧ (split-++ˡ s₁ Δ₁))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ l ⟧ᶜ) p)
          (sq-pair-Wcore s₁ Δ₁)
      ∙ ∙-ap₂' (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (pair-path Ξ₁ Δ₁) (ap ⟦_⟧ᶜ p)

    ZW : PathP (λ k → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ΞP k) ⟦ A ⊗ B ⟧ᵗ)
           (castₘ S₂'
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = []} (castₘ S₀' W) (eval Q)))
           (castₘ (⟦split⟧ s) (castₘ (pair-path Γ₁ Δ₁) PQ))
    ZW = hom-over sq-pair-W
           (hom-∙P (symP (castₘ-filler S₂'
                      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = []}
                        (castₘ S₀' W) (eval Q))))
           (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦split⟧ s₁ (~ k)} {Ξ = []} (Z (~ k)) (eval Q))
           (hom-∙P (castₘ-filler (pair-path Γ₁ Δ₁) PQ)
                   (castₘ-filler (⟦split⟧ s) (castₘ (pair-path Γ₁ Δ₁) PQ)))))

    SegP : PathP (λ k → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ΞP k) ⟦ A ⊗ B ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ []}
               (castₘ S₂'
                 (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = []}
                   (castₘ S₀' W) (eval Q)))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval ⦅ P , Q ⦆)) (eval g))
    SegP k = M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ΞP k} (ZW k) (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ Cp)
             ∙ (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁)
             ∙ (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁)
             ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ []
             ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞP)))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁)
               ∙ (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁)
               ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ []
               ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞP))))
           (ap sym (ap-∙ ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
            ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁))
                    (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
      ∙ ap (λ v' → (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁)))
                   ∙ (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁)
                   ∙ (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁)
                   ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [] ∙ v'))))
           (ap-∙ (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (pair-path Ξ₁ Δ₁) (ap ⟦_⟧ᶜ p))
      ∙ chain-conj (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
          (sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δ₁)))
          (sym (pair-path (Θ ++ Γ ++ Ξ₁) Δ₁))
          (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ []) (⟦⟧-++₂ Θ Γ Ξ₁))
          (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [])
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (pair-path Ξ₁ Δ₁))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p))
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                  ∙ (K ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)))
           (sq-tot-pair₀ Θ Γ Ξ₁ Δ₁)
      ∙ sym (conj-nat (⟦⟧-++₂ Θ Γ) p)

-- ==========================================================================
-- Squares for the pair handler, slot in the right component.
-- ==========================================================================

private
  ∙-ap₆ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e e' e'' : X}
          (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ e') (u : e' ≡ e'')
        → ap f p ∙ (ap f q ∙ (ap f r ∙ (ap f s ∙ (ap f t ∙ ap f u))))
        ≡ ap f (p ∙ (q ∙ (r ∙ (s ∙ (t ∙ u)))))
  ∙-ap₆ f p q r s t u =
    ap (ap f p ∙_) (∙-ap₅ f q r s t u) ∙ ∙-ap₂' f p (q ∙ (r ∙ (s ∙ (t ∙ u))))

  sq-stepᵣ₆ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
              {a b c d e e' e'' : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ e')
              (u : e' ≡ e'') {v' : a ≡ e''}
            → p ∙ (q ∙ (r ∙ (s ∙ (t ∙ u)))) ≡ v'
            → ap f p ∙ (ap f q ∙ (ap f r ∙ (ap f s ∙ (ap f t ∙ ap f u)))) ≡ ap f v'
  sq-stepᵣ₆ f p q r s t u eq = ∙-ap₆ f p q r s t u ∙ ap (ap f) eq

  chain6-shift : ∀ {ℓ} {X : Type ℓ} {a b c d e f' g' h' : X}
                 (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f')
                 (u : f' ≡ g') (c' : g' ≡ h')
               → p ∙ (q ∙ (r ∙ (s ∙ (t ∙ (u ∙ c')))))
               ≡ (p ∙ (q ∙ (r ∙ (s ∙ (t ∙ u))))) ∙ c'
  chain6-shift p q r s t u c' =
      ap (λ z' → p ∙ (q ∙ (r ∙ (s ∙ z')))) (∙-assoc t u c')
    ∙ ap (λ z' → p ∙ (q ∙ (r ∙ z'))) (∙-assoc s (t ∙ u) c')
    ∙ ap (λ z' → p ∙ (q ∙ z')) (∙-assoc r (s ∙ (t ∙ u)) c')
    ∙ ap (p ∙_) (∙-assoc q (r ∙ (s ∙ (t ∙ u))) c')
    ∙ ∙-assoc p (q ∙ (r ∙ (s ∙ (t ∙ u)))) c'

  chain-conj₆ : ∀ {ℓ} {X : Type ℓ} {a₀ a b c d e f' g' h' : X}
                (d' : a₀ ≡ a)
                (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f')
                (u : f' ≡ g') (c' : g' ≡ h')
              → (d' ∙ p) ∙ (q ∙ (r ∙ (s ∙ (t ∙ (u ∙ c')))))
              ≡ d' ∙ ((p ∙ (q ∙ (r ∙ (s ∙ (t ∙ u))))) ∙ c')
  chain-conj₆ d' p q r s t u c' =
      sym (∙-assoc d' p (q ∙ (r ∙ (s ∙ (t ∙ (u ∙ c'))))))
    ∙ ap (d' ∙_) (chain6-shift p q r s t u c')

  -- Two-sided cons step: LHS a right-nested 4-chain, RHS a 2-chain.
  sq-step₄₂ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d e e' : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : a ≡ e') (u : e' ≡ e)
            → p ∙ (q ∙ (r ∙ s)) ≡ t ∙ u
            → ap f p ∙ (ap f q ∙ (ap f r ∙ ap f s)) ≡ ap f t ∙ ap f u
  sq-step₄₂ f p q r s t u eq =
    ∙-ap₄ f p q r s ∙ ap (ap f) eq ∙ sym (∙-ap₂' f t u)

  -- Base of the pair-right outer bridge (induction on the split).
  sq-pairR-Wbase : ∀ {x : Ty} {Θ₂ Δ₁ Ξ : Ctx} (s₂ : Split x Θ₂ Δ₁ Ξ)
    → sym (++-assoc ⟦ Θ₂ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) [])
      ∙ (ap (λ l → l ++ []) (sym (⟦split⟧ s₂))
      ∙ (++-idr ⟦ Δ₁ ⟧ᶜ ∙ ⟦split⟧ s₂))
    ≡ ap (λ l → ⟦ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ)
      ∙ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ [] Θ₂))
  sq-pairR-Wbase here      = ∙-idl _ ∙ ∙-idl _
  sq-pairR-Wbase {x = x} {Ξ = Ξ} (there {a = A'} s₂') =
    sq-step₄₂ (⟦ A' ⟧ᵗ ∷_)
      (sym (++-assoc ⟦ _ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) []))
      (ap (λ l → l ++ []) (sym (⟦split⟧ s₂')))
      (++-idr ⟦ _ ⟧ᶜ)
      (⟦split⟧ s₂')
      (ap (λ l → ⟦ _ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ [] _)))
      (sq-pairR-Wbase s₂')

  -- The p-free core of the pair-right total square (Γ₁, then Θ₂, then Γ).
  sq-tot-pairR₀ : ∀ (Γ₁ Θ₂ Γ Ξ : Ctx)
    → sym (ap ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ))
      ∙ (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ))
      ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ)
      ∙ (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ [])
      ∙ (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ)
      ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂))))))
    ≡ ⟦⟧-++₂ (Γ₁ ++ Θ₂) Γ Ξ
  sq-tot-pairR₀ (A ∷ Γ₁) Θ₂ Γ Ξ =
    sq-stepᵣ₆ (⟦ A ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ)))
      (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ)))
      (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ))
      (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ []))
      (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
      (sq-tot-pairR₀ Γ₁ Θ₂ Γ Ξ)
  sq-tot-pairR₀ [] (A ∷ Θ₂) Γ Ξ =
    sq-stepᵣ₆ (⟦ A ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenʳ [] Θ₂ Γ Ξ)))
      (sym (pair-path [] (Θ₂ ++ Γ ++ Ξ)))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ))
      (sym (assocₘ-boundary ⟦ [] ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ []))
      (ap (λ l → (⟦ [] ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ [] Θ₂)))
      (sq-tot-pairR₀ [] Θ₂ Γ Ξ)
  sq-tot-pairR₀ [] [] (B ∷ Γ) Ξ =
    sq-stepᵣ₆ (⟦ B ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenʳ [] [] Γ Ξ)))
      (sym (pair-path [] (Γ ++ Ξ)))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ [] Γ Ξ))
      (sym (assocₘ-boundary ⟦ [] ⟧ᶜ ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ []))
      (ap (λ l → (⟦ [] ⟧ᶜ ++ ⟦ [] ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ [] [])))
      (sq-tot-pairR₀ [] [] Γ Ξ)
  sq-tot-pairR₀ [] [] [] Ξ =
      ∙-idl _
    ∙ ap (sym (++-idr ⟦ Ξ ⟧ᶜ) ∙_)
        ( ∙-idl _
        ∙ ∙-idl _
        ∙ ∙-idr (++-idr ⟦ Ξ ⟧ᶜ) )
    ∙ ∙-invl (++-idr ⟦ Ξ ⟧ᶜ)

-- ==========================================================================
-- Pair handler, slot in the right component: rewrite by the IH under the
-- pair composite, reassociate (assocₘ), and land via the view's soundness
-- square (the trailing [] absorbed by ++-idr on the diagonal).
-- ==========================================================================

core-pair-right : ∀ {x A B : Ty} {Γ₁ Δ₁ Θ₂ Ξ Θ Γ : Ctx}
    (s₂ : Split x Θ₂ Δ₁ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
    {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (co : PathP (λ k → Split x (q k) (Γ₁ ++ Δ₁) Ξ) (split-++ʳ Γ₁ s₂) s)
    (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x)
    (IHQ : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ₂ Γ Ξ i) ⟦ B ⟧ᵗ)
             (eval (sub s₂ Q g))
             (M._∘ₘ_ {Θ = ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ} (castₘ (⟦split⟧ s₂) (eval Q)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ A ⊗ B ⟧ᵗ)
      (eval (sub-pair (on-right s₂ q co) P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval ⦅ P , Q ⦆)) (eval g))
core-pair-right {x} {A} {B} {Γ₁} {Δ₁} {Θ₂} {Ξ} {Θ} {Γ} s₂ q {s} co P Q g IHQ =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast CR ⦅ P , sub s₂ Q g ⦆))
    (hom-∙P (symP (castₘ-filler (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ)) inner0))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP (IHQ i))
    (hom-∙P (symP (M.assocₘ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} {Φ = ⟦ Θ₂ ⟧ᶜ} {Ψ = ⟦ Ξ ⟧ᶜ}
                     {Ρ = ⟦ Γ ⟧ᶜ} uP uQ' (eval g)))
            SegQ))))
  where
    u₂ : M.Homₘ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ A ⊗ B ⟧ᵗ
    u₂ = uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])

    uP : M.Homₘ (⟦ Γ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ []) ⟦ A ⊗ B ⟧ᵗ
    uP = M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} u₂ (eval P)

    uQ' : M.Homₘ (⟦ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ B ⟧ᵗ
    uQ' = castₘ (⟦split⟧ s₂) (eval Q)

    CR : Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ Θ ++ Γ ++ Ξ
    CR = flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q

    inner0 : M.Homₘ (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ++ Γ ++ Ξ ⟧ᶜ ++ []) ⟦ A ⊗ B ⟧ᵗ
    inner0 = M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP (eval (sub s₂ Q g))

    WR' : M.Homₘ ((⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ ⟧ᶜ ++ [])) ⟦ A ⊗ B ⟧ᵗ
    WR' = castₘ (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
            (M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP uQ')

    PQ' : M.Homₘ (⟦ Γ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ []) ⟦ A ⊗ B ⟧ᵗ
    PQ' = M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP (eval Q)

    ΘQ : ⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    ΘQ = sym (⟦⟧-++ Γ₁ Θ₂) ∙ ap ⟦_⟧ᶜ q

    sq-ZQcore : sym (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
                ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂))
                ∙ (pair-path Γ₁ Δ₁ ∙ ⟦split⟧ (split-++ʳ Γ₁ s₂)))
              ≡ ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ)
                ∙ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂))
    sq-ZQcore = go Γ₁
      where
        go : ∀ (Γ₁' : Ctx)
           → sym (slot-unbury ⟦ Γ₁' ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
             ∙ (ap (λ l → ⟦ Γ₁' ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂))
             ∙ (pair-path Γ₁' Δ₁ ∙ ⟦split⟧ (split-++ʳ Γ₁' s₂)))
           ≡ ap (λ l → (⟦ Γ₁' ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ)
             ∙ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁' Θ₂))
        go []        = sq-pairR-Wbase s₂
        go (A' ∷ Γ₁') =
          sq-step₄₂ (⟦ A' ⟧ᵗ ∷_)
            (sym (slot-unbury ⟦ Γ₁' ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ []))
            (ap (λ l → ⟦ Γ₁' ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂)))
            (pair-path Γ₁' Δ₁)
            (⟦split⟧ (split-++ʳ Γ₁' s₂))
            (ap (λ l → (⟦ Γ₁' ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ))
            (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁' Θ₂)))
            (go Γ₁')

    sq-ZQ : sym (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
            ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂))
            ∙ (pair-path Γ₁ Δ₁ ∙ ⟦split⟧ s))
          ≡ (λ k → ΘQ k ++ ⟦ x ⟧ᵗ ∷ ++-idr ⟦ Ξ ⟧ᶜ k)
    sq-ZQ =
        ap (λ w' → sym (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
                   ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂))
                   ∙ (pair-path Γ₁ Δ₁ ∙ w')))
           (sym (square→∙ʳ (λ k → ⟦split⟧ (co k))))
      ∙ chain4-extend
          (sym (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ []))
          (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (sym (⟦split⟧ s₂)))
          (pair-path Γ₁ Δ₁)
          (⟦split⟧ (split-++ʳ Γ₁ s₂))
          (ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q)
          sq-ZQcore
      ∙ sym (∙-assoc (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ))
                     (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
                     (ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q))
      ∙ ap (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (++-idr ⟦ Ξ ⟧ᶜ) ∙_)
           (∙-ap₂' (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)) (ap ⟦_⟧ᶜ q))
      ∙ sym (diag-∙ (λ Θ' Ξ' → Θ' ++ ⟦ x ⟧ᵗ ∷ Ξ') ΘQ (++-idr ⟦ Ξ ⟧ᶜ))

    ZQ : PathP (λ k → M.Homₘ (ΘQ k ++ ⟦ x ⟧ᵗ ∷ ++-idr ⟦ Ξ ⟧ᶜ k) ⟦ A ⊗ B ⟧ᵗ)
           WR'
           (castₘ (⟦split⟧ s) (castₘ (pair-path Γ₁ Δ₁) PQ'))
    ZQ = hom-over sq-ZQ
           (hom-∙P (symP (castₘ-filler (slot-unbury ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ [])
                      (M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP uQ')))
           (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []} uP
                            (castₘ-filler (⟦split⟧ s₂) (eval Q) (~ k)))
           (hom-∙P (castₘ-filler (pair-path Γ₁ Δ₁) PQ')
                   (castₘ-filler (⟦split⟧ s) (castₘ (pair-path Γ₁ Δ₁) PQ')))))

    SegQ : PathP (λ k → M.Homₘ (ΘQ k ++ ⟦ Γ ⟧ᶜ ++ ++-idr ⟦ Ξ ⟧ᶜ k) ⟦ A ⊗ B ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ ++ []} WR' (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval ⦅ P , Q ⦆)) (eval g))
    SegQ k = M._∘ₘ_ {Θ = ΘQ k} {Ξ = ++-idr ⟦ Ξ ⟧ᶜ k} (ZQ k) (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ CR)
             ∙ (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ))
             ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ)
             ∙ (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ [])
             ∙ (λ k → ΘQ k ++ ⟦ Γ ⟧ᶜ ++ ++-idr ⟦ Ξ ⟧ᶜ k))))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ))
               ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ)
               ∙ (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ [])
               ∙ (λ k → ΘQ k ++ ⟦ Γ ⟧ᶜ ++ ++-idr ⟦ Ξ ⟧ᶜ k)))))
           (ap sym (ap-∙ ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ) (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
            ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ))
                    (ap ⟦_⟧ᶜ (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)))
      ∙ ap (λ v' → (sym (ap ⟦_⟧ᶜ (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ)))
                   ∙ (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ))
                   ∙ (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ)
                   ∙ (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ []) ∙ v'))))
           ( diag-∙ (λ Θ' Ξ' → Θ' ++ ⟦ Γ ⟧ᶜ ++ Ξ') ΘQ (++-idr ⟦ Ξ ⟧ᶜ)
           ∙ ap (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ) ∙_)
                (ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)) (ap ⟦_⟧ᶜ q)) )
      ∙ chain-conj₆ (sym (ap ⟦_⟧ᶜ (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)))
          (sym (ap ⟦_⟧ᶜ (flattenʳ Γ₁ Θ₂ Γ Ξ)))
          (sym (pair-path Γ₁ (Θ₂ ++ Γ ++ Ξ)))
          (ap (λ l → ⟦ Γ₁ ⟧ᶜ ++ l ++ []) (⟦⟧-++₂ Θ₂ Γ Ξ))
          (sym (assocₘ-boundary ⟦ Γ₁ ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ []))
          (ap (λ l → (⟦ Γ₁ ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (++-idr ⟦ Ξ ⟧ᶜ))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γ₁ Θ₂)))
          (ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q)
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (λ Θ' → Θ' ++ Γ ++ Ξ) q))
                  ∙ (K ∙ ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
           (sq-tot-pairR₀ Γ₁ Θ₂ Γ Ξ)
      ∙ sym (conj-nat (λ Θ' → ⟦⟧-++₂ Θ' Γ Ξ) q)

-- ==========================================================================
-- Naturality of unplug in a disjoint slot: plugging g' into a slot in the
-- prefix (resp. suffix) region commutes with unplug.  By injectivity of the
-- universality equivalence: apply (- ∘ₘ uM Υ), reduce with interchangeₘ and
-- the counit, and cancel the paired transports.
-- ==========================================================================

private
  Homf : M.Obₘ → List M.Obₘ → Type h'
  Homf z Ω' = M.Homₘ Ω' z

unplug-nat-l : ∀ (T₁ : List M.Obₘ) {x' : M.Obₘ} (T₂ Υ X : List M.Obₘ)
    {Λ : List M.Obₘ} {z : M.Obₘ}
    (k : M.Homₘ (T₁ ++ x' ∷ (T₂ ++ Υ ++ X)) z) (g' : M.Homₘ Λ x')
  → unplug (T₁ ++ Λ ++ T₂) Υ X
      (castₘ (sym (interchangeₘ-boundary T₁ Λ T₂ Υ X))
        (M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ Υ ++ X} k g'))
  ≡ castₘ (interchange-slot₁ T₁ Λ T₂ (⊗M Υ) X)
      (M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ ⊗M Υ ∷ X}
        (castₘ (++-assoc T₁ (x' ∷ T₂) (⊗M Υ ∷ X))
          (unplug (T₁ ++ x' ∷ T₂) Υ X
            (castₘ (sym (++-assoc T₁ (x' ∷ T₂) (Υ ++ X))) k)))
        g')
unplug-nat-l T₁ {x'} T₂ Υ X {Λ} {z} k g' =
    ap (equiv→inverse eqv) (sym step)
  ∙ equiv→unit eqv (castₘ S₁ (M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ ⊗M Υ ∷ X} U' g'))
  where
    eqv = uM-universal Υ {Θ = T₁ ++ Λ ++ T₂} {Ξ = X} {z = z}

    α : T₁ ++ x' ∷ (T₂ ++ Υ ++ X) ≡ (T₁ ++ x' ∷ T₂) ++ Υ ++ X
    α = sym (++-assoc T₁ (x' ∷ T₂) (Υ ++ X))

    β : (T₁ ++ x' ∷ T₂) ++ ⊗M Υ ∷ X ≡ T₁ ++ x' ∷ (T₂ ++ ⊗M Υ ∷ X)
    β = ++-assoc T₁ (x' ∷ T₂) (⊗M Υ ∷ X)

    S₁ : T₁ ++ Λ ++ T₂ ++ ⊗M Υ ∷ X ≡ (T₁ ++ Λ ++ T₂) ++ ⊗M Υ ∷ X
    S₁ = interchange-slot₁ T₁ Λ T₂ (⊗M Υ) X

    bnd = interchangeₘ-boundary T₁ Λ T₂ Υ X

    U : M.Homₘ ((T₁ ++ x' ∷ T₂) ++ ⊗M Υ ∷ X) z
    U = unplug (T₁ ++ x' ∷ T₂) Υ X (castₘ α k)

    U' : M.Homₘ (T₁ ++ x' ∷ (T₂ ++ ⊗M Υ ∷ X)) z
    U' = castₘ β U

    step : M._∘ₘ_ {Θ = T₁ ++ Λ ++ T₂} {Ξ = X}
             (castₘ S₁ (M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ ⊗M Υ ∷ X} U' g')) (uM Υ)
         ≡ castₘ (sym bnd) (M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ Υ ++ X} k g')
    step =
        sym (transport⁻transport (ap (Homf z) bnd) _)
      ∙ ap (castₘ (sym bnd))
          ( from-pathp (M.interchangeₘ {Θ = T₁} {Μ = T₂} {Κ = X} {Γ = Λ} {Δ = Υ}
              U' g' (uM Υ))
          ∙ ap (λ f → M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ Υ ++ X}
                        (castₘ (interchange-slot₂ T₁ x' T₂ Υ X) f) g')
              ( ap (λ f → M._∘ₘ_ {Θ = T₁ ++ x' ∷ T₂} {Ξ = X} f (uM Υ))
                   (transport⁻transport (ap (Homf z) β) U)
              ∙ equiv→counit (uM-universal Υ {Θ = T₁ ++ x' ∷ T₂} {Ξ = X} {z = z})
                  (castₘ α k) )
          ∙ ap (λ f → M._∘ₘ_ {Θ = T₁} {Ξ = T₂ ++ Υ ++ X} f g')
              (transport⁻transport (ap (Homf z) α) k) )

unplug-nat-r : ∀ (T Υ X₁ : List M.Obₘ) {x' : M.Obₘ} (X₂ : List M.Obₘ)
    {Λ : List M.Obₘ} {z : M.Obₘ}
    (k : M.Homₘ (T ++ Υ ++ (X₁ ++ x' ∷ X₂)) z) (g' : M.Homₘ Λ x')
  → unplug T Υ (X₁ ++ Λ ++ X₂)
      (castₘ (interchangeₘ-boundary T Υ X₁ Λ X₂)
        (M._∘ₘ_ {Θ = T ++ Υ ++ X₁} {Ξ = X₂}
          (castₘ (interchange-slot₁ T Υ X₁ x' X₂) k) g'))
  ≡ castₘ (interchange-slot₂ T (⊗M Υ) X₁ Λ X₂)
      (M._∘ₘ_ {Θ = T ++ ⊗M Υ ∷ X₁} {Ξ = X₂}
        (castₘ (interchange-slot₀ T (⊗M Υ) X₁ x' X₂)
          (unplug T Υ (X₁ ++ x' ∷ X₂) k))
        g')
unplug-nat-r T Υ X₁ {x'} X₂ {Λ} {z} k g' =
    ap (equiv→inverse eqvr) (sym stepr)
  ∙ equiv→unit eqvr
      (castₘ (interchange-slot₂ T (⊗M Υ) X₁ Λ X₂)
        (M._∘ₘ_ {Θ = T ++ ⊗M Υ ∷ X₁} {Ξ = X₂}
          (castₘ (interchange-slot₀ T (⊗M Υ) X₁ x' X₂) U) g'))
  where
    eqvr = uM-universal Υ {Θ = T} {Ξ = X₁ ++ Λ ++ X₂} {z = z}

    U : M.Homₘ (T ++ ⊗M Υ ∷ (X₁ ++ x' ∷ X₂)) z
    U = unplug T Υ (X₁ ++ x' ∷ X₂) k

    stepr : M._∘ₘ_ {Θ = T} {Ξ = X₁ ++ Λ ++ X₂}
              (castₘ (interchange-slot₂ T (⊗M Υ) X₁ Λ X₂)
                (M._∘ₘ_ {Θ = T ++ ⊗M Υ ∷ X₁} {Ξ = X₂}
                  (castₘ (interchange-slot₀ T (⊗M Υ) X₁ x' X₂) U) g'))
              (uM Υ)
          ≡ castₘ (interchangeₘ-boundary T Υ X₁ Λ X₂)
              (M._∘ₘ_ {Θ = T ++ Υ ++ X₁} {Ξ = X₂}
                (castₘ (interchange-slot₁ T Υ X₁ x' X₂) k) g')
    stepr =
        sym (from-pathp (M.interchangeₘ {Θ = T} {Μ = X₁} {Κ = X₂} {Γ = Υ} {Δ = Λ}
               U (uM Υ) g'))
      ∙ ap (castₘ (interchangeₘ-boundary T Υ X₁ Λ X₂))
          (ap (λ f → M._∘ₘ_ {Θ = T ++ Υ ++ X₁} {Ξ = X₂}
                       (castₘ (interchange-slot₁ T Υ X₁ x' X₂) f) g')
              (equiv→counit (uM-universal Υ {Θ = T} {Ξ = X₁ ++ x' ∷ X₂} {z = z}) k))

-- ==========================================================================
-- Squares for the match⊗ handler, slot in the Γ-region (the substitution
-- goes under the binder; the g-plug passes the unplug by unplug-nat-l).
-- ==========================================================================

private
  -- Bridge of the unplug argument from the clause's casts to the
  -- unplug-nat-l input (Θ, then Γ; the Ξ₁ level is uniform).
  sq-mAQ : ∀ (Θ Γ Ξ₁ Δm : Ctx) (AB : Ctx)
    → sym (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) AB Δm)
      ∙ (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (AB ++ Δm))
      ∙ (⟦⟧-++₂ Θ Γ (Ξ₁ ++ AB ++ Δm)
      ∙ (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++₂ Ξ₁ AB Δm)
      ∙ sym (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ AB ⟧ᶜ ⟦ Δm ⟧ᶜ))))
    ≡ ap (λ l → l ++ ⟦ AB ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ Γ Ξ₁)
  sq-mAQ (A' ∷ Θ) Γ Ξ₁ Δm AB =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) AB Δm))
      (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (AB ++ Δm)))
      (⟦⟧-++₂ Θ Γ (Ξ₁ ++ AB ++ Δm))
      (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++₂ Ξ₁ AB Δm))
      (sym (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ AB ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (sq-mAQ Θ Γ Ξ₁ Δm AB)
  sq-mAQ [] (B' ∷ Γ) Ξ₁ Δm AB =
    sq-stepᵣ₅ (⟦ B' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ (Γ ++ Ξ₁) AB Δm))
      (ap ⟦_⟧ᶜ (flattenˡ [] Γ Ξ₁ (AB ++ Δm)))
      (⟦⟧-++₂ [] Γ (Ξ₁ ++ AB ++ Δm))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++₂ Ξ₁ AB Δm))
      (sym (interchangeₘ-boundary ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ AB ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (sq-mAQ [] Γ Ξ₁ Δm AB)
  sq-mAQ [] [] Ξ₁ Δm AB =
      ap (sym (⟦⟧-++₂ Ξ₁ AB Δm) ∙_)
        (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr (⟦⟧-++₂ Ξ₁ AB Δm))
    ∙ ∙-invl (⟦⟧-++₂ Ξ₁ AB Δm)

  -- Bridge of the unplug argument across the split (induction on s₁).
  sq-mAU : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (AB Δm : Ctx)
    → sym (⟦⟧-++₂ Γm AB Δm)
      ∙ (⟦split⟧ (split-++ˡ s₁ (AB ++ Δm))
      ∙ (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++₂ Ξ₁ AB Δm)
      ∙ sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ AB ⟧ᶜ ++ ⟦ Δm ⟧ᶜ))))
    ≡ ap (λ l → l ++ ⟦ AB ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦split⟧ s₁)
  sq-mAU {x = x} {Ξ₁ = Ξ₁} here AB Δm =
      ap (sym (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++₂ Ξ₁ AB Δm)) ∙_)
        (∙-idl _ ∙ ∙-idr (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++₂ Ξ₁ AB Δm)))
    ∙ ∙-invl (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++₂ Ξ₁ AB Δm))
  sq-mAU {x = x} {Ξ₁ = Ξ₁} (there {Θ = Θ'} {Ρ = Γm'} {a = A'} s₁') AB Δm =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ Γm' AB Δm))
      (⟦split⟧ (split-++ˡ s₁' (AB ++ Δm)))
      (ap (λ l → ⟦ Θ' ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++₂ Ξ₁ AB Δm))
      (sym (++-assoc ⟦ Θ' ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ AB ⟧ᶜ ++ ⟦ Δm ⟧ᶜ)))
      (sq-mAU s₁' AB Δm)

  -- The outer-bridge core square of the match-left handler (induction on
  -- the split).
  sq-mWcore : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (Ψ Δm : Ctx)
    → sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ))
      ∙ (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦split⟧ s₁))
      ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ (split-++ˡ s₁ (Ψ ++ Δm))))
    ≡ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm))
  sq-mWcore {x = x} {Ξ₁ = Ξ₁} here Ψ Δm =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ∙-idr (sym (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++₂ Ξ₁ Ψ Δm)))
  sq-mWcore {x = x} {Ξ₁ = Ξ₁} (there {Θ = Θ'} {Ρ = Γm'} {a = A'} s₁') Ψ Δm =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (++-assoc ⟦ Θ' ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ)))
      (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦split⟧ s₁')))
      (sym (⟦⟧-++₂ Γm' Ψ Δm))
      (⟦split⟧ (split-++ˡ s₁' (Ψ ++ Δm)))
      (sq-mWcore s₁' Ψ Δm)

  -- The p-free core of the match-left total square (Θ then Γ).
  sq-tot-m₀ : ∀ (Θ Γ Ξ₁ Ψ Δm : Ctx)
    → sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm)))
      ∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
      ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ Γ Ξ₁)
      ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Δm ⟧ᶜ
      ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)))))
    ≡ ⟦⟧-++₂ Θ Γ (Ξ₁ ++ Ψ ++ Δm)
  sq-tot-m₀ (A' ∷ Θ) Γ Ξ₁ Ψ Δm =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm))))
      (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm)
      (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ Γ Ξ₁))
      (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Δm ⟧ᶜ)
      (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)))
      (sq-tot-m₀ Θ Γ Ξ₁ Ψ Δm)
  sq-tot-m₀ [] (B' ∷ Γ) Ξ₁ Ψ Δm =
    sq-stepᵣ₅ (⟦ B' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenˡ [] Γ Ξ₁ (Ψ ++ Δm))))
      (⟦⟧-++₂ (Γ ++ Ξ₁) Ψ Δm)
      (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ [] Γ Ξ₁))
      (interchangeₘ-boundary ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Δm ⟧ᶜ)
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)))
      (sq-tot-m₀ [] Γ Ξ₁ Ψ Δm)
  sq-tot-m₀ [] [] Ξ₁ Ψ Δm =
      ∙-idl _
    ∙ ap (⟦⟧-++₂ Ξ₁ Ψ Δm ∙_) (∙-idl _ ∙ ∙-idl _)
    ∙ ∙-invr (⟦⟧-++₂ Ξ₁ Ψ Δm)

-- ==========================================================================
-- match⊗ handler, slot in the Γ-region: the substitution goes under the
-- binder; rewrite by the IH inside the unplug argument, pass the g-plug
-- through the unplug (unplug-nat-l), interchange it with the scrutinee
-- plug, and land via the view's soundness square.
-- ==========================================================================

core-match⊗-ˡL : ∀ {x C A B : Ty} {Θ Γm Ξ₁ Ψ Δm Ξ Γ : Ctx}
    (s₁ : Split x Θ Γm Ξ₁) (p : Ξ₁ ++ Ψ ++ Δm ≡ Ξ)
    {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co : PathP (λ k → Split x Θ (Γm ++ Ψ ++ Δm) (p k)) (split-++ˡ s₁ (Ψ ++ Δm)) s)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    (IHQ : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ (Ξ₁ ++ A ∷ B ∷ Δm) i) ⟦ C ⟧ᵗ)
             (eval (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ++ A ∷ B ∷ Δm ⟧ᶜ}
               (castₘ (⟦split⟧ (split-++ˡ s₁ (A ∷ B ∷ Δm))) (eval Q)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match⊗ˡ (on-left s₁ p co) P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match⊗-ˡL {x} {C} {A} {B} {Θ} {Γm} {Ξ₁} {Ψ} {Δm} {Ξ} {Γ} s₁ p {s} co P Q g IHQ =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast Cm (match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Q')))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm)) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦⟧-++₂ Θ Γ Ξ₁ i} {Ξ = DC}
               (unplug (⟦⟧-++₂ Θ Γ Ξ₁ i) ABm DC (AQ i)) (eval P))
    (hom-∙P (homog-m ◁ I-m) SegM))))
  where
    AB : Ctx
    AB = A ∷ B ∷ []

    ABm DC E₂ : List M.Obₘ
    ABm = ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []
    DC  = ⟦ Δm ⟧ᶜ
    E₂  = ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ

    Cm : (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ Δm ≡ Θ ++ Γ ++ Ξ
    Cm = flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p

    Q' : Tm ((Θ ++ Γ ++ Ξ₁) ++ A ∷ B ∷ Δm) C
    Q' = cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
           (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g)

    core2 : M.Homₘ (⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ} {Ξ = DC}
              (unplug ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ ABm DC
                (castₘ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) AB Δm) (eval Q')))
              (eval P)

    ξ : ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ A ∷ B ∷ Δm ⟧ᶜ
      ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC)
    ξ = ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++₂ Ξ₁ AB Δm)

    kQ : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC)) ⟦ C ⟧ᵗ
    kQ = castₘ ξ (castₘ (⟦split⟧ (split-++ˡ s₁ (A ∷ B ∷ Δm))) (eval Q))

    bnd : (⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ) ++ ABm ++ DC
        ≡ ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ (⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC)
    bnd = interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ABm DC

    α : ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC)
      ≡ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ABm ++ DC
    α = sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (ABm ++ DC))

    β : (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⊗M ABm ∷ DC
      ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ⊗M ABm ∷ DC)
    β = ++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⊗M ABm ∷ DC)

    U₁ : M.Homₘ ((⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⊗M ABm ∷ DC) ⟦ C ⟧ᵗ
    U₁ = unplug (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ABm DC (castₘ α kQ)

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M ABm ∷ DC) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ ABm DC (castₘ (⟦⟧-++₂ Γm AB Δm) (eval Q))

    AQ : PathP (λ i → M.Homₘ (ap (λ l → l ++ ABm ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁) i) ⟦ C ⟧ᵗ)
           (castₘ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) AB Δm) (eval Q'))
           (castₘ (sym bnd)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC} kQ (eval g)))
    AQ = hom-over (sq-mAQ Θ Γ Ξ₁ Δm AB)
           (hom-∙P (symP (castₘ-filler (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) AB Δm) (eval Q')))
           (hom-∙P (symP (eval-cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
                      (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g)))
           (hom-∙P IHQ
           (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦⟧-++₂ Ξ₁ AB Δm i}
                      (castₘ-filler ξ
                        (castₘ (⟦split⟧ (split-++ˡ s₁ (A ∷ B ∷ Δm))) (eval Q)) i)
                      (eval g))
                   (castₘ-filler (sym bnd)
                     (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC} kQ (eval g)))))))

    homog-m : M._∘ₘ_ {Θ = E₂} {Ξ = DC}
                (unplug E₂ ABm DC
                  (castₘ (sym bnd)
                    (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ABm ++ DC} kQ (eval g))))
                (eval P)
            ≡ M._∘ₘ_ {Θ = E₂} {Ξ = DC}
                (castₘ (interchange-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                  (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⊗M ABm ∷ DC}
                    (castₘ β U₁) (eval g)))
                (eval P)
    homog-m = ap (λ f → M._∘ₘ_ {Θ = E₂} {Ξ = DC} f (eval P))
                (unplug-nat-l ⟦ Θ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ABm DC kQ (eval g))

    I-m : PathP (λ i → M.Homₘ
                   (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC i) ⟦ C ⟧ᵗ)
            (M._∘ₘ_ {Θ = E₂} {Ξ = DC}
              (castₘ (interchange-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⊗M ABm ∷ DC}
                  (castₘ β U₁) (eval g)))
              (eval P))
            (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC}
              (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                  (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                    (castₘ β U₁))
                  (eval P)))
              (eval g))
    I-m = M.interchangeₘ {Θ = ⟦ Θ ⟧ᶜ} {Μ = ⟦ Ξ₁ ⟧ᶜ} {Κ = DC} {Γ = ⟦ Γ ⟧ᶜ} {Δ = ⟦ Ψ ⟧ᶜ}
            (castₘ β U₁) (eval g) (eval P)

    AU : PathP (λ i → M.Homₘ (ap (λ l → l ++ ABm ++ DC) (⟦split⟧ s₁) i) ⟦ C ⟧ᵗ)
           (castₘ (⟦⟧-++₂ Γm AB Δm) (eval Q))
           (castₘ α kQ)
    AU = hom-over (sq-mAU s₁ AB Δm)
           (hom-∙P (symP (castₘ-filler (⟦⟧-++₂ Γm AB Δm) (eval Q)))
           (hom-∙P (castₘ-filler (⟦split⟧ (split-++ˡ s₁ (A ∷ B ∷ Δm))) (eval Q))
           (hom-∙P (castₘ-filler ξ
                      (castₘ (⟦split⟧ (split-++ˡ s₁ (A ∷ B ∷ Δm))) (eval Q)))
                   (castₘ-filler α kQ))))

    ΞM : ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC ≡ ⟦ Ξ ⟧ᶜ
    ΞM = sym (⟦⟧-++₂ Ξ₁ Ψ Δm) ∙ ap ⟦_⟧ᶜ p

    homog-zm : M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                 (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                   (castₘ β U₁))
                 (eval P)
             ≡ M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC} U₁ (eval P)
    homog-zm = ap (λ f → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC} f (eval P))
                 (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) β) U₁)

    sq-mW : sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
            ∙ (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) ΞM
    sq-mW =
        ap (λ w' → sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                   ∙ (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           (sym (square→∙ʳ (λ k → ⟦split⟧ (co k))))
      ∙ chain4-extend
          (sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC))
          (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ˡ s₁ (Ψ ++ Δm)))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ l ⟧ᶜ) p)
          (sq-mWcore s₁ Ψ Δm)
      ∙ ∙-ap₂' (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)) (ap ⟦_⟧ᶜ p)

    ZM : PathP (λ k' → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ΞM k') ⟦ C ⟧ᵗ)
           (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
               (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                 (castₘ β U₁))
               (eval P)))
           (castₘ (⟦split⟧ s)
             (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
               (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P))))
    ZM = hom-over sq-mW
           (hom-∙P (symP (castₘ-filler (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                        (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                          (castₘ β U₁))
                        (eval P))))
           (hom-∙P (homog-zm ◁ (λ k' → M._∘ₘ_ {Θ = ⟦split⟧ s₁ (~ k')} {Ξ = DC}
                      (unplug (⟦split⟧ s₁ (~ k')) ABm DC (AU (~ k'))) (eval P)))
           (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))
                   (castₘ-filler (⟦split⟧ s)
                     (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))))))

    SegM : PathP (λ k' → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ΞM k') ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC}
               (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                 (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                   (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M ABm) DC)
                     (castₘ β U₁))
                   (eval P)))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegM k' = M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ΞM k'} (ZM k') (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ Cm)
             ∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
             ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
             ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC
             ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞM)))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
               ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
               ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC
               ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞM))))
           (ap sym (ap-∙ ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm)) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
            ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm)))
                    (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
      ∙ ap (λ v' → (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm))))
                   ∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
                   ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
                   ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC ∙ v'))))
           (ap-∙ (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)) (ap ⟦_⟧ᶜ p))
      ∙ chain-conj (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
          (sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm))))
          (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm)
          (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁))
          (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p))
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                  ∙ (K ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)))
           (sq-tot-m₀ Θ Γ Ξ₁ Ψ Δm)
      ∙ sym (conj-nat (⟦⟧-++₂ Θ Γ) p)

-- ==========================================================================
-- Squares for the match⊗ handler, slot in the scrutinee (two nested views:
-- q for the Γ-region, p for the Δ-region — their moves commute by an
-- exchange square).
-- ==========================================================================

private
  -- Independent coordinate moves commute.
  exchange : ∀ {ℓa ℓb ℓc} {X : Type ℓa} {Y : Type ℓb} {Z : Type ℓc}
             (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
             (u : x₀ ≡ x₁) (v : y₀ ≡ y₁)
           → ap (λ x' → f x' y₀) u ∙ ap (f x₁) v
           ≡ ap (f x₀) v ∙ ap (λ x' → f x' y₁) u
  exchange f u v = sym (square→commutes (λ i j → f (u j) (v i)))

  -- Core of the scrutinee-slot outer bridge (Γm, then the split).
  sq-⊗ʳL-core : ∀ {x : Ty} (Γm : Ctx) {Θ₂ Ψ Ξ₁ : Ctx}
                (s₁ : Split x Θ₂ Ψ Ξ₁) (Δm : Ctx)
    → sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ)
      ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (sym (⟦split⟧ s₁))
      ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm))))
    ≡ ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δm))
      ∙ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))
  sq-⊗ʳL-core {x = x} (A' ∷ Γm) {Θ₂ = Θ₂} {Ξ₁ = Ξ₁} s₁ Δm =
    sq-step₄₂ (⟦ A' ⟧ᵗ ∷_)
      (sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (sym (⟦split⟧ s₁)))
      (sym (⟦⟧-++₂ Γm _ Δm))
      (⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm)))
      (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δm)))
      (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂)))
      (sq-⊗ʳL-core Γm s₁ Δm)
  sq-⊗ʳL-core [] {Ξ₁ = Ξ₁} here Δm = ∙-idl _ ∙ ∙-idl _
  sq-⊗ʳL-core {x = x} [] {Ξ₁ = Ξ₁} (there {Θ = Θ₂'} {Ρ = Ψ'} {a = A'} s₁') Δm =
    sq-step₄₂ (⟦ A' ⟧ᵗ ∷_)
      (sym (slot-unbury ⟦ [] ⟧ᶜ ⟦ Θ₂' ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (sym (⟦split⟧ s₁')))
      (sym (⟦⟧-++₂ [] Ψ' Δm))
      (⟦split⟧ (split-++ʳ [] (split-++ˡ s₁' Δm)))
      (ap (λ l → (⟦ [] ⟧ᶜ ++ ⟦ Θ₂' ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δm)))
      (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ [] Θ₂')))
      (sq-⊗ʳL-core [] s₁' Δm)

  -- The p,q-free core of the scrutinee-slot total square (Γm, Θ₂, then Γ).
  sq-⊗ʳL-tot₀ : ∀ (Γm Θ₂ Γ Ξ₁ Δm : Ctx)
    → sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm))
      ∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
      ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
      ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ)
      ∙ (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm))
      ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))))))
    ≡ ⟦⟧-++₂ (Γm ++ Θ₂) Γ (Ξ₁ ++ Δm)
  sq-⊗ʳL-tot₀ (A' ∷ Γm) Θ₂ Γ Ξ₁ Δm =
    sq-stepᵣ₆ (⟦ A' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
      (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm)
      (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ₂ Γ Ξ₁))
      (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm)))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂)))
      (sq-⊗ʳL-tot₀ Γm Θ₂ Γ Ξ₁ Δm)
  sq-⊗ʳL-tot₀ [] (A' ∷ Θ₂) Γ Ξ₁ Δm =
    sq-stepᵣ₆ (⟦ A' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenᵐ [] Θ₂ Γ Ξ₁ Δm)))
      (⟦⟧-++₂ [] (Θ₂ ++ Γ ++ Ξ₁) Δm)
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ₂ Γ Ξ₁))
      (sym (assocₘ-boundary ⟦ [] ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (ap (λ l → (⟦ [] ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm)))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ [] Θ₂)))
      (sq-⊗ʳL-tot₀ [] Θ₂ Γ Ξ₁ Δm)
  sq-⊗ʳL-tot₀ [] [] (B' ∷ Γ) Ξ₁ Δm =
    sq-stepᵣ₆ (⟦ B' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (flattenᵐ [] [] Γ Ξ₁ Δm)))
      (⟦⟧-++₂ [] (Γ ++ Ξ₁) Δm)
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ [] Γ Ξ₁))
      (sym (assocₘ-boundary ⟦ [] ⟧ᶜ ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
      (ap (λ l → (⟦ [] ⟧ᶜ ++ ⟦ [] ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm)))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ [] [])))
      (sq-⊗ʳL-tot₀ [] [] Γ Ξ₁ Δm)
  sq-⊗ʳL-tot₀ [] [] [] Ξ₁ Δm =
      ∙-idl _
    ∙ ap (⟦⟧-++ Ξ₁ Δm ∙_)
        (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr (sym (⟦⟧-++ Ξ₁ Δm)))
    ∙ ∙-invr (⟦⟧-++ Ξ₁ Δm)

  -- Double conjugation: pull the q- and p-conjugates out of a 6-chain.
  chain-conj₆₂ : ∀ {ℓ} {X : Type ℓ} {a₀ a₁ a b c d e f' g' h' k' : X}
                 (d₁ : a₀ ≡ a₁) (d₂ : a₁ ≡ a)
                 (p₁ : a ≡ b) (p₂ : b ≡ c) (p₃ : c ≡ d) (p₄ : d ≡ e)
                 (p₅ : e ≡ f') (p₆ : f' ≡ g') (cp : g' ≡ h') (cq : h' ≡ k')
               → ((d₁ ∙ d₂) ∙ p₁) ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (p₆ ∙ (cp ∙ cq))))))
               ≡ d₁ ∙ ((d₂ ∙ ((p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ p₆))))) ∙ cp)) ∙ cq)
  chain-conj₆₂ d₁ d₂ p₁ p₂ p₃ p₄ p₅ p₆ cp cq =
      ap (_∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (p₆ ∙ (cp ∙ cq)))))))
         (sym (∙-assoc d₁ d₂ p₁))
    ∙ sym (∙-assoc d₁ (d₂ ∙ p₁) (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (p₆ ∙ (cp ∙ cq)))))))
    ∙ ap (d₁ ∙_)
        ( chain-conj₆ d₂ p₁ p₂ p₃ p₄ p₅ p₆ (cp ∙ cq)
        ∙ ap (d₂ ∙_) (∙-assoc (p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ p₆))))) cp cq)
        ∙ ∙-assoc d₂ ((p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ p₆))))) ∙ cp) cq )

-- ==========================================================================
-- match⊗ handler, slot in the scrutinee: rewrite by the IH under the
-- unplugged continuation, reassociate (assocₘ), and land through both
-- nested views' soundness squares (their moves exchanged).
-- ==========================================================================

core-match⊗-ʳL : ∀ {x C A B : Ty} {Γm Θ₂ Ψ Ξ₁ Δm Ξ Θ Γ : Ctx}
    (s₁ : Split x Θ₂ Ψ Ξ₁) (p : Ξ₁ ++ Δm ≡ Ξ) (q : Γm ++ Θ₂ ≡ Θ)
    {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co' : PathP (λ k → Split x Θ₂ (Ψ ++ Δm) (p k)) (split-++ˡ s₁ Δm) s')
    (co  : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    (IHP : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ₂ Γ Ξ₁ i) ⟦ A ⊗ B ⟧ᵗ)
             (eval (sub s₁ P g))
             (M._∘ₘ_ {Θ = ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ}
               (castₘ (⟦split⟧ s₁) (eval P)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match⊗ʳ (on-left s₁ p co') q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match⊗-ʳL {x} {C} {A} {B} {Γm} {Θ₂} {Ψ} {Ξ₁} {Δm} {Ξ} {Θ} {Γ}
  s₁ p q {s'} {s} co' co P Q g IHP =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast Cm2 (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P g) Q)))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm)) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (IHP i))
    (hom-∙P (symP (M.assocₘ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} {Φ = ⟦ Θ₂ ⟧ᶜ} {Ψ = ⟦ Ξ₁ ⟧ᶜ}
                     {Ρ = ⟦ Γ ⟧ᶜ} UQ u₁ (eval g)))
            SegZ))))
  where
    AB : Ctx
    AB = A ∷ B ∷ []

    ABm DC : List M.Obₘ
    ABm = ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []
    DC  = ⟦ Δm ⟧ᶜ

    Cm2 : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ Θ ++ Γ ++ Ξ
    Cm2 = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ (λ i → q i ++ Γ ++ p i)

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M ABm ∷ DC) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ ABm DC (castₘ (⟦⟧-++₂ Γm AB Δm) (eval Q))

    u₁ : M.Homₘ (⟦ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ A ⊗ B ⟧ᵗ
    u₁ = castₘ (⟦split⟧ s₁) (eval P)

    core2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ++ Γ ++ Ξ₁ ⟧ᶜ ++ DC) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval (sub s₁ P g))

    Θ2E : ⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    Θ2E = sym (⟦⟧-++ Γm Θ₂) ∙ ap ⟦_⟧ᶜ q

    ΞE2 : ⟦ Ξ₁ ⟧ᶜ ++ DC ≡ ⟦ Ξ ⟧ᶜ
    ΞE2 = sym (⟦⟧-++ Ξ₁ Δm) ∙ ap ⟦_⟧ᶜ p

    K5 = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δm))
    K6 = ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))
    Lp = ap (λ l → ⟦ Γm ++ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ l ⟧ᶜ) p
    Lq = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q
    P5x = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (ap ⟦_⟧ᶜ p)
    K6x = ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))

    sq-Z2-fin : ((K5 ∙ K6) ∙ Lp) ∙ Lq ≡ (λ k → Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k)
    sq-Z2-fin =
        ap (_∙ Lq) (sym (∙-assoc K5 K6 Lp))
      ∙ ap (λ z' → (K5 ∙ z') ∙ Lq)
           (exchange (λ ΘL ΞL → ΘL ++ ⟦ x ⟧ᵗ ∷ ΞL) (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ p))
      ∙ ap (_∙ Lq) (∙-assoc K5 P5x K6x)
      ∙ ap (λ z' → (z' ∙ K6x) ∙ Lq)
           (∙-ap₂' (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l)
             (sym (⟦⟧-++ Ξ₁ Δm)) (ap ⟦_⟧ᶜ p))
      ∙ sym (∙-assoc (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) ΞE2) K6x Lq)
      ∙ ap (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) ΞE2 ∙_)
           (∙-ap₂' (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ q))
      ∙ sym (diag-∙ (λ ΘL ΞL → ΘL ++ ⟦ x ⟧ᵗ ∷ ΞL) Θ2E ΞE2)

    sq-Z2 : sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
            ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ (λ k → Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k)
    sq-Z2 =
        ap (λ w' → sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           ( sym (square→∙ʳ (λ k → ⟦split⟧ (co k)))
           ∙ ap (_∙ Lq) (sym (square→∙ʳ (λ k → ⟦split⟧ (split-++ʳ Γm (co' k))))) )
      ∙ chain4-extend
          (sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC))
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm)) ∙ Lp)
          Lq
          (chain4-extend
            (sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC))
            (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁)))
            (sym (⟦⟧-++₂ Γm Ψ Δm))
            (⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm)))
            Lp
            (sq-⊗ʳL-core Γm s₁ Δm))
      ∙ sq-Z2-fin

    ZR2 : PathP (λ k → M.Homₘ (Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k) ⟦ C ⟧ᵗ)
           (castₘ (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁))
           (castₘ (⟦split⟧ s)
             (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
               (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P))))
    ZR2 = hom-over sq-Z2
           (hom-∙P (symP (castₘ-filler (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁)))
           (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ
                            (castₘ-filler (⟦split⟧ s₁) (eval P) (~ k)))
           (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))
                   (castₘ-filler (⟦split⟧ s)
                     (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))))))

    SegZ : PathP (λ k → M.Homₘ (Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k) ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ DC}
               (castₘ (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                 (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegZ k = M._∘ₘ_ {Θ = Θ2E k} {Ξ = ΞE2 k} (ZR2 k) (eval g)

    K5g = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm))
    K6g = ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))
    Lp2 = ap (λ l → ⟦ Γm ++ Θ₂ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ l ⟧ᶜ) p
    Q6g = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q
    P5g = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)
    K6g' = ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))

    sq-t5 : (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k) ≡ K5g ∙ (K6g ∙ (Lp2 ∙ Q6g))
    sq-t5 =
        diag-∙ (λ ΘL ΞL → ΘL ++ ⟦ Γ ⟧ᶜ ++ ΞL) Θ2E ΞE2
      ∙ ap₂ _∙_
          (ap-∙ (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l)
            (sym (⟦⟧-++ Ξ₁ Δm)) (ap ⟦_⟧ᶜ p))
          (ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ)
            (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ q))
      ∙ sym (∙-assoc K5g P5g (K6g' ∙ Q6g))
      ∙ ap (K5g ∙_) (∙-assoc P5g K6g' Q6g)
      ∙ ap (λ z' → K5g ∙ (z' ∙ Q6g))
           (sym (exchange (λ ΘL ΞL → ΘL ++ ⟦ Γ ⟧ᶜ ++ ΞL)
              (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ p)))
      ∙ ap (K5g ∙_) (sym (∙-assoc K6g Lp2 Q6g))

    sq-tot : sym (ap ⟦_⟧ᶜ Cm2)
             ∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
             ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
             ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC)
             ∙ (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k))))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
               ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
               ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC)
               ∙ (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k)))))
           ( ap sym (ap-∙ ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm) (λ i → q i ++ Γ ++ p i)
                    ∙ ap (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm) ∙_)
                         ( ap (ap ⟦_⟧ᶜ) (diag-∙ (λ Θ' Ξ' → Θ' ++ Γ ++ Ξ') q p)
                         ∙ ap-∙ ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i) (λ i → q i ++ Γ ++ Ξ)))
           ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm))
                   (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)
                    ∙ ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
           ∙ ap (_∙ sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
                (sym-∙ (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i))
                       (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))) )
      ∙ ap (λ v' → ((sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
                     ∙ sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
                   ∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
                   ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC) ∙ v'))))
           sq-t5
      ∙ chain-conj₆₂
          (sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ)))
          (sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)))
          (sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
          (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm)
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁))
          (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC))
          K5g K6g Lp2 Q6g
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
                  ∙ ((sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)) ∙ (K ∙ Lp2)) ∙ Q6g))
           (sq-⊗ʳL-tot₀ Γm Θ₂ Γ Ξ₁ Δm)
      ∙ sym ( conj-nat (λ Θ' → ⟦⟧-++₂ Θ' Γ Ξ) q
            ∙ ap (λ z' → sym (ap (λ Θ' → ⟦ Θ' ++ Γ ++ Ξ ⟧ᶜ) q)
                         ∙ (z' ∙ ap (λ Θ' → ⟦ Θ' ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
                 (conj-nat (λ Ξ' → ⟦⟧-++₂ (Γm ++ Θ₂) Γ Ξ') p) )

-- ==========================================================================
-- Squares for the match⊗ handler, slot in the Δ-region.
-- ==========================================================================

private
  chain-conj₅₂ : ∀ {ℓ} {X : Type ℓ} {a₀ a₁ a b c d e f' g' h' : X}
                 (d₁ : a₀ ≡ a₁) (d₂ : a₁ ≡ a)
                 (p₁ : a ≡ b) (p₂ : b ≡ c) (p₃ : c ≡ d) (p₄ : d ≡ e)
                 (p₅ : e ≡ f') (cp : f' ≡ g') (cq : g' ≡ h')
               → ((d₁ ∙ d₂) ∙ p₁) ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (cp ∙ cq)))))
               ≡ d₁ ∙ ((d₂ ∙ ((p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ p₅)))) ∙ cp)) ∙ cq)
  chain-conj₅₂ d₁ d₂ p₁ p₂ p₃ p₄ p₅ cp cq =
      ap (_∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (cp ∙ cq)))))) (sym (∙-assoc d₁ d₂ p₁))
    ∙ sym (∙-assoc d₁ (d₂ ∙ p₁) (p₂ ∙ (p₃ ∙ (p₄ ∙ (p₅ ∙ (cp ∙ cq))))))
    ∙ ap (d₁ ∙_)
        ( chain-conj d₂ p₁ p₂ p₃ p₄ p₅ (cp ∙ cq)
        ∙ ap (d₂ ∙_) (∙-assoc (p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ p₅)))) cp cq)
        ∙ ∙-assoc d₂ ((p₁ ∙ (p₂ ∙ (p₃ ∙ (p₄ ∙ p₅)))) ∙ cp) cq )

  -- Bridge of the unplug argument to the unplug-nat-r input (Γm-induction;
  -- at Γm = [] everything on the binder pair reduces definitionally).
  sq-⊗ʳR-AQ : ∀ (Γm : Ctx) (A B : Ty) (Θ₃ Γ Ξ : Ctx)
    → sym (⟦⟧-++₂ Γm (A ∷ B ∷ []) (Θ₃ ++ Γ ++ Ξ))
      ∙ (ap ⟦_⟧ᶜ (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ)
      ∙ (⟦⟧-++₂ (Γm ++ A ∷ B ∷ Θ₃) Γ Ξ
      ∙ (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (⟦⟧-++₂ Γm (A ∷ B ∷ []) Θ₃)
      ∙ interchangeₘ-boundary ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)))
    ≡ ap (λ l → ⟦ Γm ⟧ᶜ ++ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
  sq-⊗ʳR-AQ (A' ∷ Γm) A B Θ₃ Γ Ξ =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ Γm (A ∷ B ∷ []) (Θ₃ ++ Γ ++ Ξ)))
      (ap ⟦_⟧ᶜ (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
      (⟦⟧-++₂ (Γm ++ A ∷ B ∷ Θ₃) Γ Ξ)
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (⟦⟧-++₂ Γm (A ∷ B ∷ []) Θ₃))
      (interchangeₘ-boundary ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
      (sq-⊗ʳR-AQ Γm A B Θ₃ Γ Ξ)
  sq-⊗ʳR-AQ [] A B Θ₃ Γ Ξ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ap (⟦⟧-++₂ (A ∷ B ∷ Θ₃) Γ Ξ ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦⟧-++₂ (A ∷ B ∷ Θ₃) Γ Ξ)

  -- Bridge of the two unplug arguments across the split (Γm-induction).
  sq-⊗ʳR-AU : ∀ (Γm : Ctx) {x A B : Ty} {Θ₃ Δm Ξ : Ctx} (s₂ : Split x Θ₃ Δm Ξ)
    → sym (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm)
      ∙ (⟦split⟧ (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂))
      ∙ (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (⟦⟧-++₂ Γm (A ∷ B ∷ []) Θ₃)
      ∙ sym (interchange-slot₁ ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ)))
    ≡ ap (λ l → ⟦ Γm ⟧ᶜ ++ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ++ l) (⟦split⟧ s₂)
  sq-⊗ʳR-AU (A' ∷ Γm) {x} {A} {B} {Θ₃} {Δm} {Ξ} s₂ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm))
      (⟦split⟧ (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)))
      (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (⟦⟧-++₂ Γm (A ∷ B ∷ []) Θ₃))
      (sym (interchange-slot₁ ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ))
      (sq-⊗ʳR-AU Γm s₂)
  sq-⊗ʳR-AU [] {x} {A} {B} {Θ₃} {Δm} {Ξ} s₂ =
      ∙-idl _
    ∙ ap (⟦split⟧ (split-++ʳ (A ∷ B ∷ []) s₂) ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦split⟧ (split-++ʳ (A ∷ B ∷ []) s₂))

  -- Outer-bridge core: the canonical splits against the clause casts
  -- (Γm, then Ψ).
  sq-⊗ʳR-Wcore : ∀ (Γm Ψ : Ctx) {x : Ty} {Θ₃ Δm Ξ : Ctx} (s₂ : Split x Θ₃ Δm Ξ)
    → sym (interchange-slot₁ ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ)
      ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂))
      ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂))))
    ≡ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))
  sq-⊗ʳR-Wcore (A' ∷ Γm) Ψ {x} {Θ₃} {Δm} {Ξ} s₂ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (interchange-slot₁ ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ))
      (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
      (sym (⟦⟧-++₂ Γm Ψ Δm))
      (⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂)))
      (sq-⊗ʳR-Wcore Γm Ψ s₂)
  sq-⊗ʳR-Wcore [] (A' ∷ Ψ) {x} {Θ₃} {Δm} {Ξ} s₂ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (interchange-slot₁ ⟦ [] ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
      (sym (⟦⟧-++₂ [] Ψ Δm))
      (⟦split⟧ (split-++ʳ [] (split-++ʳ Ψ s₂)))
      (sq-⊗ʳR-Wcore [] Ψ s₂)
  sq-⊗ʳR-Wcore [] [] {x} {Θ₃} {Δm} {Ξ} s₂ =
      ∙-idl _
    ∙ ap (sym (⟦split⟧ s₂) ∙_) (∙-idl (⟦split⟧ s₂))
    ∙ ∙-invl (⟦split⟧ s₂)

  -- The q,q₂-free core of the Δ-region total square (Γm, then Ψ).
  sq-⊗ʳR-tot₀ : ∀ (Γm Ψ Θ₃ Γ Ξ : Ctx)
    → sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ)))
      ∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
      ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
      ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
      ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)))))
    ≡ ⟦⟧-++₂ (Γm ++ Ψ ++ Θ₃) Γ Ξ
  sq-⊗ʳR-tot₀ (A' ∷ Γm) Ψ Θ₃ Γ Ξ =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
      (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ))
      (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ))
      (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)))
      (sq-⊗ʳR-tot₀ Γm Ψ Θ₃ Γ Ξ)
  sq-⊗ʳR-tot₀ [] (A' ∷ Ψ) Θ₃ Γ Ξ =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (ap ⟦_⟧ᶜ (bury [] Ψ Θ₃ (Γ ++ Ξ))))
      (⟦⟧-++₂ [] Ψ (Θ₃ ++ Γ ++ Ξ))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ))
      (sym (interchangeₘ-boundary ⟦ [] ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ))
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ [] Ψ Θ₃)))
      (sq-⊗ʳR-tot₀ [] Ψ Θ₃ Γ Ξ)
  sq-⊗ʳR-tot₀ [] [] Θ₃ Γ Ξ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ap (⟦⟧-++₂ Θ₃ Γ Ξ ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦⟧-++₂ Θ₃ Γ Ξ)

-- ==========================================================================
-- match⊗ handler, slot in the Δ-region: rewrite by the IH inside the unplug
-- argument, pass the g-plug through the unplug (unplug-nat-r), interchange
-- it with the scrutinee plug, and land through both views' soundness
-- squares (moves in the same coordinate, no exchange needed).
-- ==========================================================================

core-match⊗-ʳR : ∀ {x C A B : Ty} {Γm Ψ Θ₂ Θ₃ Δm Ξ Θ Γ : Ctx}
    (s₂ : Split x Θ₃ Δm Ξ) (q₂ : Ψ ++ Θ₃ ≡ Θ₂) (q : Γm ++ Θ₂ ≡ Θ)
    {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co₂ : PathP (λ k → Split x (q₂ k) (Ψ ++ Δm) Ξ) (split-++ʳ Ψ s₂) s')
    (co  : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
    (IHQ : PathP (λ i → M.Homₘ (⟦⟧-++₂ (Γm ++ A ∷ B ∷ Θ₃) Γ Ξ i) ⟦ C ⟧ᵗ)
             (eval (sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q g))
             (M._∘ₘ_ {Θ = ⟦ Γm ++ A ∷ B ∷ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂))) (eval Q))
               (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match⊗ʳ (on-right s₂ q₂ co₂) q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match⊗-ʳR {x} {C} {A} {B} {Γm} {Ψ} {Θ₂} {Θ₃} {Δm} {Ξ} {Θ} {Γ}
  s₂ q₂ q {s'} {s} co₂ co P Q g IHQ =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast CmR (match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P Q'')))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ))) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦⟧-++₂ Θ₃ Γ Ξ i}
               (unplug ⟦ Γm ⟧ᶜ ABm (⟦⟧-++₂ Θ₃ Γ Ξ i) (AQ2 i)) (eval P))
    (hom-∙P ( ap (λ f → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ}
                    f (eval P))
                 (unplug-nat-r ⟦ Γm ⟧ᶜ ABm ⟦ Θ₃ ⟧ᶜ ⟦ Ξ ⟧ᶜ kQ2 (eval g))
            ◁ symP (M.interchangeₘ {Θ = ⟦ Γm ⟧ᶜ} {Μ = ⟦ Θ₃ ⟧ᶜ} {Κ = ⟦ Ξ ⟧ᶜ}
                      {Γ = ⟦ Ψ ⟧ᶜ} {Δ = ⟦ Γ ⟧ᶜ} U₂ (eval P) (eval g)) )
            SegF))))
  where
    AB : Ctx
    AB = A ∷ B ∷ []

    ABm : List M.Obₘ
    ABm = ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []

    CmR : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ) ≡ Θ ++ Γ ++ Ξ
    CmR = bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q)

    sB : Split x (Γm ++ A ∷ B ∷ Θ₃) (Γm ++ A ∷ B ∷ Δm) Ξ
    sB = split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)

    Q'' : Tm (Γm ++ A ∷ B ∷ (Θ₃ ++ Γ ++ Ξ)) C
    Q'' = cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ)) (sub sB Q g)

    η' : ⟦ Γm ++ A ∷ B ∷ Θ₃ ⟧ᶜ ≡ ⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ
    η' = ⟦⟧-++₂ Γm (A ∷ B ∷ []) Θ₃

    S₁r : ⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
        ≡ (⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
    S₁r = interchange-slot₁ ⟦ Γm ⟧ᶜ ABm ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ

    YQ : M.Homₘ ((⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ
    YQ = castₘ (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η') (castₘ (⟦split⟧ sB) (eval Q))

    kQ2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ ABm ++ (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ)) ⟦ C ⟧ᵗ
    kQ2 = castₘ (sym S₁r) YQ

    U₂ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M ABm ∷ (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ)) ⟦ C ⟧ᵗ
    U₂ = unplug ⟦ Γm ⟧ᶜ ABm (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) kQ2

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M ABm ∷ ⟦ Δm ⟧ᶜ) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ ABm ⟦ Δm ⟧ᶜ (castₘ (⟦⟧-++₂ Γm AB Δm) (eval Q))

    core2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ}
              (unplug ⟦ Γm ⟧ᶜ ABm ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ
                (castₘ (⟦⟧-++₂ Γm AB (Θ₃ ++ Γ ++ Ξ)) (eval Q'')))
              (eval P)

    AU2 : PathP (λ k → M.Homₘ (⟦ Γm ⟧ᶜ ++ ABm ++ ⟦split⟧ s₂ k) ⟦ C ⟧ᵗ)
            (castₘ (⟦⟧-++₂ Γm AB Δm) (eval Q))
            kQ2
    AU2 = hom-over (sq-⊗ʳR-AU Γm s₂)
            (hom-∙P (symP (castₘ-filler (⟦⟧-++₂ Γm AB Δm) (eval Q)))
            (hom-∙P (castₘ-filler (⟦split⟧ sB) (eval Q))
            (hom-∙P (castₘ-filler (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η')
                       (castₘ (⟦split⟧ sB) (eval Q)))
                    (castₘ-filler (sym S₁r) YQ))))

    AQ2 : PathP (λ i → M.Homₘ (⟦ Γm ⟧ᶜ ++ ABm ++ ⟦⟧-++₂ Θ₃ Γ Ξ i) ⟦ C ⟧ᵗ)
            (castₘ (⟦⟧-++₂ Γm AB (Θ₃ ++ Γ ++ Ξ)) (eval Q''))
            (castₘ (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ABm ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
              (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                (castₘ S₁r kQ2) (eval g)))
    AQ2 = hom-over (sq-⊗ʳR-AQ Γm A B Θ₃ Γ Ξ)
            (hom-∙P (symP (castₘ-filler (⟦⟧-++₂ Γm AB (Θ₃ ++ Γ ++ Ξ)) (eval Q'')))
            (hom-∙P (symP (eval-cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ)) (sub sB Q g)))
            (hom-∙P IHQ
            (hom-∙P (λ i → M._∘ₘ_ {Θ = η' i} {Ξ = ⟦ Ξ ⟧ᶜ}
                       (castₘ-filler (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η')
                         (castₘ (⟦split⟧ sB) (eval Q)) i)
                       (eval g))
                    ( ap (λ f → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                             f (eval g))
                         (sym (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) (sym S₁r)) YQ))
                    ◁ castₘ-filler (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ABm ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
                        (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ABm ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                          (castₘ S₁r kQ2) (eval g)) )))))

    ΘF : ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    ΘF = sym (⟦⟧-++₂ Γm Ψ Θ₃) ∙ ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q)

    S₁ᵢ : ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
        ≡ (⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
    S₁ᵢ = interchange-slot₁ ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ

    Lq₂ Lq : _ ≡ _
    Lq₂ = ap (λ l → ⟦ Γm ++ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q₂
    Lq  = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q

    sq-WF : sym S₁ᵢ
            ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ΘF
    sq-WF =
        ap (λ w' → sym S₁ᵢ
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           ( sym (square→∙ʳ (λ k → ⟦split⟧ (co k)))
           ∙ ap (_∙ Lq) (sym (square→∙ʳ (λ k → ⟦split⟧ (split-++ʳ Γm (co₂ k))))) )
      ∙ chain4-extend (sym S₁ᵢ)
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂)) ∙ Lq₂)
          Lq
          (chain4-extend (sym S₁ᵢ)
            (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
            (sym (⟦⟧-++₂ Γm Ψ Δm))
            (⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂)))
            Lq₂
            (sq-⊗ʳR-Wcore Γm Ψ s₂))
      ∙ sym (∙-assoc (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))) Lq₂ Lq)
      ∙ ap (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)) ∙_)
           ( ∙-ap₂' (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (ap (Γm ++_) q₂) q
           ∙ ap (ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ)) refl )
      ∙ ∙-ap₂' (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))
          (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q))

    ZR3 : PathP (λ k → M.Homₘ (ΘF k ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ)
            (castₘ S₁ᵢ (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
              U₂ (eval P)))
            (castₘ (⟦split⟧ s)
              (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P))))
    ZR3 = hom-over sq-WF
            (hom-∙P (symP (castₘ-filler S₁ᵢ
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
                         U₂ (eval P))))
            (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦split⟧ s₂ (~ k)}
                       (unplug ⟦ Γm ⟧ᶜ ABm (⟦split⟧ s₂ (~ k)) (AU2 (~ k))) (eval P))
            (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P)))
                    (castₘ-filler (⟦split⟧ s)
                      (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                        (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P)))))))

    SegF : PathP (λ k → M.Homₘ (ΘF k ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ S₁ᵢ (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
                 U₂ (eval P)))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegF k = M._∘ₘ_ {Θ = ΘF k} {Ξ = ⟦ Ξ ⟧ᶜ} (ZR3 k) (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ CmR)
             ∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
             ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
             ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
             ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘF)))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
               ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
               ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
               ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘF))))
           ( ap sym (ap-∙ ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))
                       (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
                    ∙ ap (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ)) ∙_)
                         (ap (ap ⟦_⟧ᶜ) (ap-∙ (_++ Γ ++ Ξ) (ap (Γm ++_) q₂) q)
                         ∙ ap-∙ ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)) (ap (_++ Γ ++ Ξ) q)))
           ∙ sym-∙ (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ)))
                   (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))
                    ∙ ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
           ∙ ap (_∙ sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
                (sym-∙ (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)))
                       (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))) )
      ∙ ap (λ v' → ((sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
                     ∙ sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))))
                    ∙ sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
                   ∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
                   ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
                   ∙ v'))))
           ( ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))
               (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q))
           ∙ ap (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)) ∙_)
                ( ap (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ))
                     (ap-∙ ⟦_⟧ᶜ (ap (Γm ++_) q₂) q)
                ∙ ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ)
                    (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂)) (ap ⟦_⟧ᶜ q) ) )
      ∙ chain-conj₅₂
          (sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q)))
          (sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))))
          (sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
          (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ))
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ))
          (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂)))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ q))
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
                  ∙ ((sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)))
                      ∙ (K ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂))))
                     ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ q)))
           (sq-⊗ʳR-tot₀ Γm Ψ Θ₃ Γ Ξ)
      ∙ sym ( conj-nat (λ Θ' → ⟦⟧-++₂ Θ' Γ Ξ) q
            ∙ ap (λ z' → sym (ap (λ Θ' → ⟦ Θ' ++ Γ ++ Ξ ⟧ᶜ) q)
                         ∙ (z' ∙ ap (λ Θ' → ⟦ Θ' ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
                 (conj-nat (λ l → ⟦⟧-++₂ (Γm ++ l) Γ Ξ) q₂) )

-- ==========================================================================
-- Squares for the match𝟙 handlers (the nullary versions of the match⊗
-- squares; the ʳL and Wcore/tot₀ squares are Υ-independent and reused).
-- ==========================================================================

private
  sq-1AQ : ∀ (Θ Γ Ξ₁ Δm : Ctx)
    → sym (⟦⟧-++ (Θ ++ Γ ++ Ξ₁) Δm)
      ∙ (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δm)
      ∙ (⟦⟧-++₂ Θ Γ (Ξ₁ ++ Δm)
      ∙ (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++ Ξ₁ Δm)
      ∙ sym (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ))))
    ≡ ap (λ l → l ++ [] ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++₂ Θ Γ Ξ₁)
  sq-1AQ (A' ∷ Θ) Γ Ξ₁ Δm =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++ (Θ ++ Γ ++ Ξ₁) Δm))
      (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ Δm))
      (⟦⟧-++₂ Θ Γ (Ξ₁ ++ Δm))
      (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++ Ξ₁ Δm))
      (sym (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ))
      (sq-1AQ Θ Γ Ξ₁ Δm)
  sq-1AQ [] (B' ∷ Γ) Ξ₁ Δm =
    sq-stepᵣ₅ (⟦ B' ⟧ᵗ ∷_)
      (sym (⟦⟧-++ (Γ ++ Ξ₁) Δm))
      (ap ⟦_⟧ᶜ (flattenˡ [] Γ Ξ₁ Δm))
      (⟦⟧-++₂ [] Γ (Ξ₁ ++ Δm))
      (ap (λ l → ⟦ [] ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (⟦⟧-++ Ξ₁ Δm))
      (sym (interchangeₘ-boundary ⟦ [] ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ))
      (sq-1AQ [] Γ Ξ₁ Δm)
  sq-1AQ [] [] Ξ₁ Δm =
      ap (sym (⟦⟧-++ Ξ₁ Δm) ∙_)
        (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr (⟦⟧-++ Ξ₁ Δm))
    ∙ ∙-invl (⟦⟧-++ Ξ₁ Δm)

  sq-1AU : ∀ {x : Ty} {Θ Γm Ξ₁ : Ctx} (s₁ : Split x Θ Γm Ξ₁) (Δm : Ctx)
    → sym (⟦⟧-++ Γm Δm)
      ∙ (⟦split⟧ (split-++ˡ s₁ Δm)
      ∙ (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++ Ξ₁ Δm)
      ∙ sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ([] ++ ⟦ Δm ⟧ᶜ))))
    ≡ ap (λ l → l ++ [] ++ ⟦ Δm ⟧ᶜ) (⟦split⟧ s₁)
  sq-1AU {x = x} {Ξ₁ = Ξ₁} here Δm =
      ap (sym (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++ Ξ₁ Δm)) ∙_)
        (∙-idl _ ∙ ∙-idr (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++ Ξ₁ Δm)))
    ∙ ∙-invl (ap (⟦ x ⟧ᵗ ∷_) (⟦⟧-++ Ξ₁ Δm))
  sq-1AU {x = x} {Ξ₁ = Ξ₁} (there {Θ = Θ'} {Ρ = Γm'} {a = A'} s₁') Δm =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++ Γm' Δm))
      (⟦split⟧ (split-++ˡ s₁' Δm))
      (ap (λ l → ⟦ Θ' ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++ Ξ₁ Δm))
      (sym (++-assoc ⟦ Θ' ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ([] ++ ⟦ Δm ⟧ᶜ)))
      (sq-1AU s₁' Δm)

  sq-1ʳR-AQ : ∀ (Γm : Ctx) (Θ₃ Γ Ξ : Ctx)
    → sym (⟦⟧-++ Γm (Θ₃ ++ Γ ++ Ξ))
      ∙ (ap ⟦_⟧ᶜ (flattenʳ Γm Θ₃ Γ Ξ)
      ∙ (⟦⟧-++₂ (Γm ++ Θ₃) Γ Ξ
      ∙ (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (⟦⟧-++ Γm Θ₃)
      ∙ interchangeₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)))
    ≡ ap (λ l → ⟦ Γm ⟧ᶜ ++ [] ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
  sq-1ʳR-AQ (A' ∷ Γm) Θ₃ Γ Ξ =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++ Γm (Θ₃ ++ Γ ++ Ξ)))
      (ap ⟦_⟧ᶜ (flattenʳ Γm Θ₃ Γ Ξ))
      (⟦⟧-++₂ (Γm ++ Θ₃) Γ Ξ)
      (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (⟦⟧-++ Γm Θ₃))
      (interchangeₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
      (sq-1ʳR-AQ Γm Θ₃ Γ Ξ)
  sq-1ʳR-AQ [] Θ₃ Γ Ξ =
      ∙-idl _
    ∙ ∙-idl _
    ∙ ap (⟦⟧-++₂ Θ₃ Γ Ξ ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦⟧-++₂ Θ₃ Γ Ξ)

  sq-1ʳR-AU : ∀ (Γm : Ctx) {x : Ty} {Θ₃ Δm Ξ : Ctx} (s₂ : Split x Θ₃ Δm Ξ)
    → sym (⟦⟧-++ Γm Δm)
      ∙ (⟦split⟧ (split-++ʳ Γm s₂)
      ∙ (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (⟦⟧-++ Γm Θ₃)
      ∙ sym (interchange-slot₁ ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ)))
    ≡ ap (λ l → ⟦ Γm ⟧ᶜ ++ [] ++ l) (⟦split⟧ s₂)
  sq-1ʳR-AU (A' ∷ Γm) {x} {Θ₃} {Δm} {Ξ} s₂ =
    sq-stepᵣ₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++ Γm Δm))
      (⟦split⟧ (split-++ʳ Γm s₂))
      (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (⟦⟧-++ Γm Θ₃))
      (sym (interchange-slot₁ ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ))
      (sq-1ʳR-AU Γm s₂)
  sq-1ʳR-AU [] {x} {Θ₃} {Δm} {Ξ} s₂ =
      ∙-idl _
    ∙ ap (⟦split⟧ s₂ ∙_) (∙-idl refl)
    ∙ ∙-idr (⟦split⟧ s₂)

-- ==========================================================================
-- match𝟙 handler, slot in the Γ-region (nullary version of core-match⊗-ˡL).
-- ==========================================================================

core-match𝟙-ˡL : ∀ {x C : Ty} {Θ Γm Ξ₁ Ψ Δm Ξ Γ : Ctx}
    (s₁ : Split x Θ Γm Ξ₁) (p : Ξ₁ ++ Ψ ++ Δm ≡ Ξ)
    {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co : PathP (λ k → Split x Θ (Γm ++ Ψ ++ Δm) (p k)) (split-++ˡ s₁ (Ψ ++ Δm)) s)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x)
    (IHQ : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ (Ξ₁ ++ Δm) i) ⟦ C ⟧ᵗ)
             (eval (sub (split-++ˡ s₁ Δm) Q g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ++ Δm ⟧ᶜ}
               (castₘ (⟦split⟧ (split-++ˡ s₁ Δm)) (eval Q)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match𝟙ˡ (on-left s₁ p co) P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match𝟙-ˡL {x} {C} {Θ} {Γm} {Ξ₁} {Ψ} {Δm} {Ξ} {Γ} s₁ p {s} co P Q g IHQ =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast Cm (match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P Q')))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm)) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦⟧-++₂ Θ Γ Ξ₁ i} {Ξ = DC}
               (unplug (⟦⟧-++₂ Θ Γ Ξ₁ i) [] DC (AQ i)) (eval P))
    (hom-∙P (homog-m ◁ I-m) SegM))))
  where
    DC E₂ : List M.Obₘ
    DC  = ⟦ Δm ⟧ᶜ
    E₂  = ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ

    Cm : (Θ ++ Γ ++ Ξ₁) ++ Ψ ++ Δm ≡ Θ ++ Γ ++ Ξ
    Cm = flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p

    Q' : Tm ((Θ ++ Γ ++ Ξ₁) ++ Δm) C
    Q' = cast (sym (flattenˡ Θ Γ Ξ₁ Δm)) (sub (split-++ˡ s₁ Δm) Q g)

    core2 : M.Homₘ (⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ} {Ξ = DC}
              (unplug ⟦ Θ ++ Γ ++ Ξ₁ ⟧ᶜ [] DC
                (castₘ (⟦⟧-++ (Θ ++ Γ ++ Ξ₁) Δm) (eval Q')))
              (eval P)

    ξ : ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ
      ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC)
    ξ = ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (⟦⟧-++ Ξ₁ Δm)

    kQ : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC)) ⟦ C ⟧ᵗ
    kQ = castₘ ξ (castₘ (⟦split⟧ (split-++ˡ s₁ Δm)) (eval Q))

    bnd : (⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ⟧ᶜ) ++ [] ++ DC
        ≡ ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ (⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC)
    bnd = interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ [] DC

    α : ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC)
      ≡ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ [] ++ DC
    α = sym (++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ([] ++ DC))

    β : (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⊗M [] ∷ DC
      ≡ ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ (⟦ Ξ₁ ⟧ᶜ ++ ⊗M [] ∷ DC)
    β = ++-assoc ⟦ Θ ⟧ᶜ (⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) (⊗M [] ∷ DC)

    U₁ : M.Homₘ ((⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ++ ⊗M [] ∷ DC) ⟦ C ⟧ᵗ
    U₁ = unplug (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) [] DC (castₘ α kQ)

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M [] ∷ DC) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ [] DC (castₘ (⟦⟧-++ Γm Δm) (eval Q))

    AQ : PathP (λ i → M.Homₘ (ap (λ l → l ++ [] ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁) i) ⟦ C ⟧ᵗ)
           (castₘ (⟦⟧-++ (Θ ++ Γ ++ Ξ₁) Δm) (eval Q'))
           (castₘ (sym bnd)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC} kQ (eval g)))
    AQ = hom-over (sq-1AQ Θ Γ Ξ₁ Δm)
           (hom-∙P (symP (castₘ-filler (⟦⟧-++ (Θ ++ Γ ++ Ξ₁) Δm) (eval Q')))
           (hom-∙P (symP (eval-cast (sym (flattenˡ Θ Γ Ξ₁ Δm))
                      (sub (split-++ˡ s₁ Δm) Q g)))
           (hom-∙P IHQ
           (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦⟧-++ Ξ₁ Δm i}
                      (castₘ-filler ξ
                        (castₘ (⟦split⟧ (split-++ˡ s₁ Δm)) (eval Q)) i)
                      (eval g))
                   (castₘ-filler (sym bnd)
                     (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC} kQ (eval g)))))))

    homog-m : M._∘ₘ_ {Θ = E₂} {Ξ = DC}
                (unplug E₂ [] DC
                  (castₘ (sym bnd)
                    (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ [] ++ DC} kQ (eval g))))
                (eval P)
            ≡ M._∘ₘ_ {Θ = E₂} {Ξ = DC}
                (castₘ (interchange-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                  (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⊗M [] ∷ DC}
                    (castₘ β U₁) (eval g)))
                (eval P)
    homog-m = ap (λ f → M._∘ₘ_ {Θ = E₂} {Ξ = DC} f (eval P))
                (unplug-nat-l ⟦ Θ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ [] DC kQ (eval g))

    I-m : PathP (λ i → M.Homₘ
                   (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC i) ⟦ C ⟧ᵗ)
            (M._∘ₘ_ {Θ = E₂} {Ξ = DC}
              (castₘ (interchange-slot₁ ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⊗M [] ∷ DC}
                  (castₘ β U₁) (eval g)))
              (eval P))
            (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC}
              (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                  (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                    (castₘ β U₁))
                  (eval P)))
              (eval g))
    I-m = M.interchangeₘ {Θ = ⟦ Θ ⟧ᶜ} {Μ = ⟦ Ξ₁ ⟧ᶜ} {Κ = DC} {Γ = ⟦ Γ ⟧ᶜ} {Δ = ⟦ Ψ ⟧ᶜ}
            (castₘ β U₁) (eval g) (eval P)

    AU : PathP (λ i → M.Homₘ (ap (λ l → l ++ [] ++ DC) (⟦split⟧ s₁) i) ⟦ C ⟧ᵗ)
           (castₘ (⟦⟧-++ Γm Δm) (eval Q))
           (castₘ α kQ)
    AU = hom-over (sq-1AU s₁ Δm)
           (hom-∙P (symP (castₘ-filler (⟦⟧-++ Γm Δm) (eval Q)))
           (hom-∙P (castₘ-filler (⟦split⟧ (split-++ˡ s₁ Δm)) (eval Q))
           (hom-∙P (castₘ-filler ξ
                      (castₘ (⟦split⟧ (split-++ˡ s₁ Δm)) (eval Q)))
                   (castₘ-filler α kQ))))

    ΞM : ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC ≡ ⟦ Ξ ⟧ᶜ
    ΞM = sym (⟦⟧-++₂ Ξ₁ Ψ Δm) ∙ ap ⟦_⟧ᶜ p

    homog-zm : M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                 (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                   (castₘ β U₁))
                 (eval P)
             ≡ M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC} U₁ (eval P)
    homog-zm = ap (λ f → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC} f (eval P))
                 (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) β) U₁)

    sq-mW : sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
            ∙ (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) ΞM
    sq-mW =
        ap (λ w' → sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                   ∙ (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           (sym (square→∙ʳ (λ k → ⟦split⟧ (co k))))
      ∙ chain4-extend
          (sym (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC))
          (sym (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦split⟧ s₁)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ˡ s₁ (Ψ ++ Δm)))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ l ⟧ᶜ) p)
          (sq-mWcore s₁ Ψ Δm)
      ∙ ∙-ap₂' (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)) (ap ⟦_⟧ᶜ p)

    ZM : PathP (λ k' → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ΞM k') ⟦ C ⟧ᵗ)
           (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
               (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                 (castₘ β U₁))
               (eval P)))
           (castₘ (⟦split⟧ s)
             (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
               (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P))))
    ZM = hom-over sq-mW
           (hom-∙P (symP (castₘ-filler (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                        (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                          (castₘ β U₁))
                        (eval P))))
           (hom-∙P (homog-zm ◁ (λ k' → M._∘ₘ_ {Θ = ⟦split⟧ s₁ (~ k')} {Ξ = DC}
                      (unplug (⟦split⟧ s₁ (~ k')) [] DC (AU (~ k'))) (eval P)))
           (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))
                   (castₘ-filler (⟦split⟧ s)
                     (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))))))

    SegM : PathP (λ k' → M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ΞM k') ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ DC}
               (castₘ (interchange-slot₂ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
                 (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ} {Ξ = DC}
                   (castₘ (interchange-slot₀ ⟦ Θ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ (⊗M []) DC)
                     (castₘ β U₁))
                   (eval P)))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegM k' = M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ΞM k'} (ZM k') (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ Cm)
             ∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
             ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
             ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC
             ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞM)))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
               ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
               ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC
               ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) ΞM))))
           (ap sym (ap-∙ ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm)) (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
            ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm)))
                    (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
      ∙ ap (λ v' → (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm))))
                   ∙ (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm
                   ∙ (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁)
                   ∙ (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC ∙ v'))))
           (ap-∙ (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)) (ap ⟦_⟧ᶜ p))
      ∙ chain-conj (sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)))
          (sym (ap ⟦_⟧ᶜ (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm))))
          (⟦⟧-++₂ (Θ ++ Γ ++ Ξ₁) Ψ Δm)
          (ap (λ l → l ++ ⟦ Ψ ⟧ᶜ ++ DC) (⟦⟧-++₂ Θ Γ Ξ₁))
          (interchangeₘ-boundary ⟦ Θ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ ⟦ Ψ ⟧ᶜ DC)
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++₂ Ξ₁ Ψ Δm)))
          (ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p))
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (λ Ξ' → Θ ++ Γ ++ Ξ') p))
                  ∙ (K ∙ ap (λ l → ⟦ Θ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)))
           (sq-tot-m₀ Θ Γ Ξ₁ Ψ Δm)
      ∙ sym (conj-nat (⟦⟧-++₂ Θ Γ) p)

-- ==========================================================================
-- match𝟙 handler, slot in the scrutinee (nullary version of core-match⊗-ʳL;
-- the squares are Υ-independent and reused verbatim).
-- ==========================================================================

core-match𝟙-ʳL : ∀ {x C : Ty} {Γm Θ₂ Ψ Ξ₁ Δm Ξ Θ Γ : Ctx}
    (s₁ : Split x Θ₂ Ψ Ξ₁) (p : Ξ₁ ++ Δm ≡ Ξ) (q : Γm ++ Θ₂ ≡ Θ)
    {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co' : PathP (λ k → Split x Θ₂ (Ψ ++ Δm) (p k)) (split-++ˡ s₁ Δm) s')
    (co  : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x)
    (IHP : PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ₂ Γ Ξ₁ i) ⟦ 𝟙 ⟧ᵗ)
             (eval (sub s₁ P g))
             (M._∘ₘ_ {Θ = ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ}
               (castₘ (⟦split⟧ s₁) (eval P)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match𝟙ʳ (on-left s₁ p co') q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match𝟙-ʳL {x} {C} {Γm} {Θ₂} {Ψ} {Ξ₁} {Δm} {Ξ} {Θ} {Γ}
  s₁ p q {s'} {s} co' co P Q g IHP =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast Cm2 (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P g) Q)))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm)) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (IHP i))
    (hom-∙P (symP (M.assocₘ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} {Φ = ⟦ Θ₂ ⟧ᶜ} {Ψ = ⟦ Ξ₁ ⟧ᶜ}
                     {Ρ = ⟦ Γ ⟧ᶜ} UQ u₁ (eval g)))
            SegZ))))
  where
    DC : List M.Obₘ
    DC = ⟦ Δm ⟧ᶜ

    Cm2 : Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δm) ≡ Θ ++ Γ ++ Ξ
    Cm2 = flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ (λ i → q i ++ Γ ++ p i)

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M [] ∷ DC) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ [] DC (castₘ (⟦⟧-++ Γm Δm) (eval Q))

    u₁ : M.Homₘ (⟦ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ⟧ᶜ) ⟦ 𝟙 ⟧ᵗ
    u₁ = castₘ (⟦split⟧ s₁) (eval P)

    core2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ++ Γ ++ Ξ₁ ⟧ᶜ ++ DC) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval (sub s₁ P g))

    Θ2E : ⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    Θ2E = sym (⟦⟧-++ Γm Θ₂) ∙ ap ⟦_⟧ᶜ q

    ΞE2 : ⟦ Ξ₁ ⟧ᶜ ++ DC ≡ ⟦ Ξ ⟧ᶜ
    ΞE2 = sym (⟦⟧-++ Ξ₁ Δm) ∙ ap ⟦_⟧ᶜ p

    K5 = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (sym (⟦⟧-++ Ξ₁ Δm))
    K6 = ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))
    Lp = ap (λ l → ⟦ Γm ++ Θ₂ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ l ⟧ᶜ) p
    Lq = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q
    P5x = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) (ap ⟦_⟧ᶜ p)
    K6x = ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))

    sq-Z2-fin : ((K5 ∙ K6) ∙ Lp) ∙ Lq ≡ (λ k → Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k)
    sq-Z2-fin =
        ap (_∙ Lq) (sym (∙-assoc K5 K6 Lp))
      ∙ ap (λ z' → (K5 ∙ z') ∙ Lq)
           (exchange (λ ΘL ΞL → ΘL ++ ⟦ x ⟧ᵗ ∷ ΞL) (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ p))
      ∙ ap (_∙ Lq) (∙-assoc K5 P5x K6x)
      ∙ ap (λ z' → (z' ∙ K6x) ∙ Lq)
           (∙-ap₂' (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l)
             (sym (⟦⟧-++ Ξ₁ Δm)) (ap ⟦_⟧ᶜ p))
      ∙ sym (∙-assoc (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) ΞE2) K6x Lq)
      ∙ ap (ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ l) ΞE2 ∙_)
           (∙-ap₂' (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ q))
      ∙ sym (diag-∙ (λ ΘL ΞL → ΘL ++ ⟦ x ⟧ᵗ ∷ ΞL) Θ2E ΞE2)

    sq-Z2 : sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
            ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ (λ k → Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k)
    sq-Z2 =
        ap (λ w' → sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           ( sym (square→∙ʳ (λ k → ⟦split⟧ (co k)))
           ∙ ap (_∙ Lq) (sym (square→∙ʳ (λ k → ⟦split⟧ (split-++ʳ Γm (co' k))))) )
      ∙ chain4-extend
          (sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC))
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm)) ∙ Lp)
          Lq
          (chain4-extend
            (sym (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC))
            (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (sym (⟦split⟧ s₁)))
            (sym (⟦⟧-++₂ Γm Ψ Δm))
            (⟦split⟧ (split-++ʳ Γm (split-++ˡ s₁ Δm)))
            Lp
            (sq-⊗ʳL-core Γm s₁ Δm))
      ∙ sq-Z2-fin

    ZR2 : PathP (λ k → M.Homₘ (Θ2E k ++ ⟦ x ⟧ᵗ ∷ ΞE2 k) ⟦ C ⟧ᵗ)
           (castₘ (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁))
           (castₘ (⟦split⟧ s)
             (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
               (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P))))
    ZR2 = hom-over sq-Z2
           (hom-∙P (symP (castₘ-filler (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁)))
           (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ
                            (castₘ-filler (⟦split⟧ s₁) (eval P) (~ k)))
           (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))
                   (castₘ-filler (⟦split⟧ s)
                     (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ (eval P)))))))

    SegZ : PathP (λ k → M.Homₘ (Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k) ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ} {Ξ = ⟦ Ξ₁ ⟧ᶜ ++ DC}
               (castₘ (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ₁ ⟧ᶜ DC)
                 (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = DC} UQ u₁))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegZ k = M._∘ₘ_ {Θ = Θ2E k} {Ξ = ΞE2 k} (ZR2 k) (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ Cm2)
             ∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
             ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
             ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC)
             ∙ (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k))))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
               ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
               ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC)
               ∙ (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k)))))
           ( ap sym (ap-∙ ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm) (λ i → q i ++ Γ ++ p i)
                     ∙ ap (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm) ∙_)
                          (ap (ap ⟦_⟧ᶜ) (diag-∙ (λ Θ' Ξ' → Θ' ++ Γ ++ Ξ') q p)
                          ∙ ap-∙ ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i) (λ i → q i ++ Γ ++ Ξ)))
           ∙ sym-∙ (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm))
                   (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)
                    ∙ ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
           ∙ ap (_∙ sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
                (sym-∙ (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i))
                       (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))) )
      ∙ ap (λ v' → ((sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
                     ∙ sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)))
                    ∙ sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
                   ∙ (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁)
                   ∙ (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC) ∙ v'))))
           sq-t5
      ∙ chain-conj₆₂
          (sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ)))
          (sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)))
          (sym (ap ⟦_⟧ᶜ (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm)))
          (⟦⟧-++₂ Γm (Θ₂ ++ Γ ++ Ξ₁) Δm)
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ DC) (⟦⟧-++₂ Θ₂ Γ Ξ₁))
          (sym (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Θ₂ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ₁ ⟧ᶜ DC))
          K5g K6g Lp2 Q6g
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (λ i → q i ++ Γ ++ Ξ))
                  ∙ ((sym (ap ⟦_⟧ᶜ (λ i → (Γm ++ Θ₂) ++ Γ ++ p i)) ∙ (K ∙ Lp2)) ∙ Q6g))
           (sq-⊗ʳL-tot₀ Γm Θ₂ Γ Ξ₁ Δm)
      ∙ sym ( conj-nat (λ Θ' → ⟦⟧-++₂ Θ' Γ Ξ) q
            ∙ ap (λ z' → sym (ap (λ Θ' → ⟦ Θ' ++ Γ ++ Ξ ⟧ᶜ) q)
                         ∙ (z' ∙ ap (λ Θ' → ⟦ Θ' ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
                 (conj-nat (λ Ξ' → ⟦⟧-++₂ (Γm ++ Θ₂) Γ Ξ') p) )
      where
        K5g = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (sym (⟦⟧-++ Ξ₁ Δm))
        K6g = ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ₁ ++ Δm ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))
        Lp2 = ap (λ l → ⟦ Γm ++ Θ₂ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ l ⟧ᶜ) p
        Q6g = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q
        P5g = ap (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l) (ap ⟦_⟧ᶜ p)
        K6g' = ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++ Γm Θ₂))

        sq-t5 : (λ k → Θ2E k ++ ⟦ Γ ⟧ᶜ ++ ΞE2 k) ≡ K5g ∙ (K6g ∙ (Lp2 ∙ Q6g))
        sq-t5 =
            diag-∙ (λ ΘL ΞL → ΘL ++ ⟦ Γ ⟧ᶜ ++ ΞL) Θ2E ΞE2
          ∙ ap₂ _∙_
              (ap-∙ (λ l → (⟦ Γm ⟧ᶜ ++ ⟦ Θ₂ ⟧ᶜ) ++ ⟦ Γ ⟧ᶜ ++ l)
                (sym (⟦⟧-++ Ξ₁ Δm)) (ap ⟦_⟧ᶜ p))
              (ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ)
                (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ q))
          ∙ sym (∙-assoc K5g P5g (K6g' ∙ Q6g))
          ∙ ap (K5g ∙_) (∙-assoc P5g K6g' Q6g)
          ∙ ap (λ z' → K5g ∙ (z' ∙ Q6g))
               (sym (exchange (λ ΘL ΞL → ΘL ++ ⟦ Γ ⟧ᶜ ++ ΞL)
                  (sym (⟦⟧-++ Γm Θ₂)) (ap ⟦_⟧ᶜ p)))
          ∙ ap (K5g ∙_) (sym (∙-assoc K6g Lp2 Q6g))

-- ==========================================================================
-- match𝟙 handler, slot in the Δ-region (nullary version of core-match⊗-ʳR).
-- ==========================================================================

core-match𝟙-ʳR : ∀ {x C : Ty} {Γm Ψ Θ₂ Θ₃ Δm Ξ Θ Γ : Ctx}
    (s₂ : Split x Θ₃ Δm Ξ) (q₂ : Ψ ++ Θ₃ ≡ Θ₂) (q : Γm ++ Θ₂ ≡ Θ)
    {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co₂ : PathP (λ k → Split x (q₂ k) (Ψ ++ Δm) Ξ) (split-++ʳ Ψ s₂) s')
    (co  : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x)
    (IHQ : PathP (λ i → M.Homₘ (⟦⟧-++₂ (Γm ++ Θ₃) Γ Ξ i) ⟦ C ⟧ᵗ)
             (eval (sub (split-++ʳ Γm s₂) Q g))
             (M._∘ₘ_ {Θ = ⟦ Γm ++ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ (split-++ʳ Γm s₂)) (eval Q)) (eval g)))
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match𝟙ʳ (on-right s₂ q₂ co₂) q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
core-match𝟙-ʳR {x} {C} {Γm} {Ψ} {Θ₂} {Θ₃} {Δm} {Ξ} {Θ} {Γ}
  s₂ q₂ q {s'} {s} co₂ co P Q g IHQ =
  hom-over sq-tot
    (hom-∙P (symP (eval-cast CmR (match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P Q'')))
    (hom-∙P (symP (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ))) core2))
    (hom-∙P (λ i → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦⟧-++₂ Θ₃ Γ Ξ i}
               (unplug ⟦ Γm ⟧ᶜ [] (⟦⟧-++₂ Θ₃ Γ Ξ i) (AQ2 i)) (eval P))
    (hom-∙P ( ap (λ f → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ}
                    f (eval P))
                 (unplug-nat-r ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ Ξ ⟧ᶜ kQ2 (eval g))
            ◁ symP (M.interchangeₘ {Θ = ⟦ Γm ⟧ᶜ} {Μ = ⟦ Θ₃ ⟧ᶜ} {Κ = ⟦ Ξ ⟧ᶜ}
                      {Γ = ⟦ Ψ ⟧ᶜ} {Δ = ⟦ Γ ⟧ᶜ} U₂ (eval P) (eval g)) )
            SegF))))
  where
    CmR : Γm ++ Ψ ++ (Θ₃ ++ Γ ++ Ξ) ≡ Θ ++ Γ ++ Ξ
    CmR = bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q)

    sB : Split x (Γm ++ Θ₃) (Γm ++ Δm) Ξ
    sB = split-++ʳ Γm s₂

    Q'' : Tm (Γm ++ (Θ₃ ++ Γ ++ Ξ)) C
    Q'' = cast (sym (flattenʳ Γm Θ₃ Γ Ξ)) (sub sB Q g)

    η' : ⟦ Γm ++ Θ₃ ⟧ᶜ ≡ ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ
    η' = ⟦⟧-++ Γm Θ₃

    S₁r : ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
        ≡ (⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
    S₁r = interchange-slot₁ ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ

    YQ : M.Homₘ ((⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ
    YQ = castₘ (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η') (castₘ (⟦split⟧ sB) (eval Q))

    kQ2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ [] ++ (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ)) ⟦ C ⟧ᵗ
    kQ2 = castₘ (sym S₁r) YQ

    U₂ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M [] ∷ (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ)) ⟦ C ⟧ᵗ
    U₂ = unplug ⟦ Γm ⟧ᶜ [] (⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) kQ2

    UQ : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⊗M [] ∷ ⟦ Δm ⟧ᶜ) ⟦ C ⟧ᵗ
    UQ = unplug ⟦ Γm ⟧ᶜ [] ⟦ Δm ⟧ᶜ (castₘ (⟦⟧-++ Γm Δm) (eval Q))

    core2 : M.Homₘ (⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ
    core2 = M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ}
              (unplug ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ++ Γ ++ Ξ ⟧ᶜ
                (castₘ (⟦⟧-++ Γm (Θ₃ ++ Γ ++ Ξ)) (eval Q'')))
              (eval P)

    AU2 : PathP (λ k → M.Homₘ (⟦ Γm ⟧ᶜ ++ [] ++ ⟦split⟧ s₂ k) ⟦ C ⟧ᵗ)
            (castₘ (⟦⟧-++ Γm Δm) (eval Q))
            kQ2
    AU2 = hom-over (sq-1ʳR-AU Γm s₂)
            (hom-∙P (symP (castₘ-filler (⟦⟧-++ Γm Δm) (eval Q)))
            (hom-∙P (castₘ-filler (⟦split⟧ sB) (eval Q))
            (hom-∙P (castₘ-filler (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η')
                       (castₘ (⟦split⟧ sB) (eval Q)))
                    (castₘ-filler (sym S₁r) YQ))))

    AQ2 : PathP (λ i → M.Homₘ (⟦ Γm ⟧ᶜ ++ [] ++ ⟦⟧-++₂ Θ₃ Γ Ξ i) ⟦ C ⟧ᵗ)
            (castₘ (⟦⟧-++ Γm (Θ₃ ++ Γ ++ Ξ)) (eval Q''))
            (castₘ (interchangeₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
              (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                (castₘ S₁r kQ2) (eval g)))
    AQ2 = hom-over (sq-1ʳR-AQ Γm Θ₃ Γ Ξ)
            (hom-∙P (symP (castₘ-filler (⟦⟧-++ Γm (Θ₃ ++ Γ ++ Ξ)) (eval Q'')))
            (hom-∙P (symP (eval-cast (sym (flattenʳ Γm Θ₃ Γ Ξ)) (sub sB Q g)))
            (hom-∙P IHQ
            (hom-∙P (λ i → M._∘ₘ_ {Θ = η' i} {Ξ = ⟦ Ξ ⟧ᶜ}
                       (castₘ-filler (ap (_++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) η')
                         (castₘ (⟦split⟧ sB) (eval Q)) i)
                       (eval g))
                    ( ap (λ f → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                             f (eval g))
                         (sym (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) (sym S₁r)) YQ))
                    ◁ castₘ-filler (interchangeₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
                        (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                          (castₘ S₁r kQ2) (eval g)) )))))

    ΘF : ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ ≡ ⟦ Θ ⟧ᶜ
    ΘF = sym (⟦⟧-++₂ Γm Ψ Θ₃) ∙ ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q)

    S₁ᵢ : ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
        ≡ (⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ) ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ
    S₁ᵢ = interchange-slot₁ ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ x ⟧ᵗ ⟦ Ξ ⟧ᶜ

    Lq₂ Lq : _ ≡ _
    Lq₂ = ap (λ l → ⟦ Γm ++ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q₂
    Lq  = ap (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) q

    sq-WF : sym S₁ᵢ
            ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂))
            ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ ⟦split⟧ s))
          ≡ ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ΘF
    sq-WF =
        ap (λ w' → sym S₁ᵢ
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂))
                   ∙ (sym (⟦⟧-++₂ Γm Ψ Δm) ∙ w')))
           ( sym (square→∙ʳ (λ k → ⟦split⟧ (co k)))
           ∙ ap (_∙ Lq) (sym (square→∙ʳ (λ k → ⟦split⟧ (split-++ʳ Γm (co₂ k))))) )
      ∙ chain4-extend (sym S₁ᵢ)
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
          (sym (⟦⟧-++₂ Γm Ψ Δm))
          (⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂)) ∙ Lq₂)
          Lq
          (chain4-extend (sym S₁ᵢ)
            (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (sym (⟦split⟧ s₂)))
            (sym (⟦⟧-++₂ Γm Ψ Δm))
            (⟦split⟧ (split-++ʳ Γm (split-++ʳ Ψ s₂)))
            Lq₂
            (sq-⊗ʳR-Wcore Γm Ψ s₂))
      ∙ sym (∙-assoc (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))) Lq₂ Lq)
      ∙ ap (ap (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)) ∙_)
           (∙-ap₂' (λ l → ⟦ l ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (ap (Γm ++_) q₂) q)
      ∙ ∙-ap₂' (λ l → l ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))
          (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q))

    ZR3 : PathP (λ k → M.Homₘ (ΘF k ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ)
            (castₘ S₁ᵢ (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
              U₂ (eval P)))
            (castₘ (⟦split⟧ s)
              (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P))))
    ZR3 = hom-over sq-WF
            (hom-∙P (symP (castₘ-filler S₁ᵢ
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
                         U₂ (eval P))))
            (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦split⟧ s₂ (~ k)}
                       (unplug ⟦ Γm ⟧ᶜ [] (⟦split⟧ s₂ (~ k)) (AU2 (~ k))) (eval P))
            (hom-∙P (castₘ-filler (sym (⟦⟧-++₂ Γm Ψ Δm))
                       (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P)))
                    (castₘ-filler (⟦split⟧ s)
                      (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
                        (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} UQ (eval P)))))))

    SegF : PathP (λ k → M.Homₘ (ΘF k ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ⟦ C ⟧ᵗ)
             (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Θ₃ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ S₁ᵢ (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Θ₃ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ}
                 U₂ (eval P)))
               (eval g))
             (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
               (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))
    SegF k = M._∘ₘ_ {Θ = ΘF k} {Ξ = ⟦ Ξ ⟧ᶜ} (ZR3 k) (eval g)

    sq-tot : sym (ap ⟦_⟧ᶜ CmR)
             ∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
             ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
             ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
             ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘF)))
           ≡ ⟦⟧-++₂ Θ Γ Ξ
    sq-tot =
        ap (_∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
               ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
               ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
               ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) ΘF))))
           ( ap sym (ap-∙ ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))
                       (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
                    ∙ ap (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ)) ∙_)
                         (ap (ap ⟦_⟧ᶜ) (ap-∙ (_++ Γ ++ Ξ) (ap (Γm ++_) q₂) q)
                         ∙ ap-∙ ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)) (ap (_++ Γ ++ Ξ) q)))
           ∙ sym-∙ (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ)))
                   (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))
                    ∙ ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
           ∙ ap (_∙ sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
                (sym-∙ (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)))
                       (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))) )
      ∙ ap (λ v' → ((sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
                     ∙ sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))))
                    ∙ sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
                   ∙ (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ)
                   ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ)
                   ∙ (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ)
                   ∙ v'))))
           ( ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃))
               (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂ ∙ q))
           ∙ ap (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)) ∙_)
                ( ap (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ))
                     (ap-∙ ⟦_⟧ᶜ (ap (Γm ++_) q₂) q)
                ∙ ap-∙ (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ)
                    (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂)) (ap ⟦_⟧ᶜ q) ) )
      ∙ chain-conj₅₂
          (sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q)))
          (sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂))))
          (sym (ap ⟦_⟧ᶜ (bury Γm Ψ Θ₃ (Γ ++ Ξ))))
          (⟦⟧-++₂ Γm Ψ (Θ₃ ++ Γ ++ Ξ))
          (ap (λ l → ⟦ Γm ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ l) (⟦⟧-++₂ Θ₃ Γ Ξ))
          (sym (interchangeₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Ψ ⟧ᶜ ⟦ Θ₃ ⟧ᶜ ⟦ Γ ⟧ᶜ ⟦ Ξ ⟧ᶜ))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (sym (⟦⟧-++₂ Γm Ψ Θ₃)))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂)))
          (ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ q))
      ∙ ap (λ K → sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) q))
                  ∙ ((sym (ap ⟦_⟧ᶜ (ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂)))
                      ∙ (K ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ (ap (Γm ++_) q₂))))
                     ∙ ap (λ l → l ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) (ap ⟦_⟧ᶜ q)))
           (sq-⊗ʳR-tot₀ Γm Ψ Θ₃ Γ Ξ)
      ∙ sym ( conj-nat (λ Θ' → ⟦⟧-++₂ Θ' Γ Ξ) q
            ∙ ap (λ z' → sym (ap (λ Θ' → ⟦ Θ' ++ Γ ++ Ξ ⟧ᶜ) q)
                         ∙ (z' ∙ ap (λ Θ' → ⟦ Θ' ⟧ᶜ ++ ⟦ Γ ⟧ᶜ ++ ⟦ Ξ ⟧ᶜ) q))
                 (conj-nat (λ l → ⟦⟧-++₂ (Γm ++ l) Γ Ξ) q₂) )

-- ==========================================================================
-- TIER 1, the substitution lemma (Theorem 2.4.10, functoriality on
-- composition): eval maps sub to _∘ₘ_, mutually with its spine analogue and
-- one dispatcher per branch handler of sub.
-- ==========================================================================

eval-sub : ∀ {x z Θ Ρ Ξ Γ} (s : Split x Θ Ρ Ξ) (t : Tm Ρ z) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ z ⟧ᵗ)
      (eval (sub s t g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ} (castₘ (⟦split⟧ s) (eval t)) (eval g))

eval-sp-sub : ∀ (Χ : List M.Obₘ) {As w} (f : M.Homₘ (Χ ++ map φ.F₀ As) w)
    {x Θ Ρ Ξ Γ} (s : Split x Θ Ρ Ξ) (ts : Sp Ρ As) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (pre-bound Χ Θ Γ Ξ i) w)
      (eval-sp Χ f (sub-sp s ts g))
      (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f ts)) (eval g))

eval-sub-pair : ∀ {x A B Θ Γ₁ Δ₁ Ξ Γ} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (v : Split-++ Γ₁ Δ₁ s) (P : Tm Γ₁ A) (Q : Tm Δ₁ B) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ A ⊗ B ⟧ᵗ)
      (eval (sub-pair v P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ} (castₘ (⟦split⟧ s) (eval ⦅ P , Q ⦆)) (eval g))

eval-sub-match⊗ˡ : ∀ {x C A B Θ Γm Ψ Δm Ξ Γ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (v : Split-++ Γm (Ψ ++ Δm) s)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match⊗ˡ v P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))

eval-sub-match⊗ʳ : ∀ {x C A B Θ₂ Ψ Δm Ξ Γm Θ Γ} {s' : Split x Θ₂ (Ψ ++ Δm) Ξ}
    (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
    {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match⊗ʳ v q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match⊗ {Γ = Γm} {Δ = Δm} P Q))) (eval g))

eval-sub-match𝟙ˡ : ∀ {x C Θ Γm Ψ Δm Ξ Γ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (v : Split-++ Γm (Ψ ++ Δm) s)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match𝟙ˡ v P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))

eval-sub-match𝟙ʳ : ∀ {x C Θ₂ Ψ Δm Ξ Γm Θ Γ} {s' : Split x Θ₂ (Ψ ++ Δm) Ξ}
    (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
    {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
    (co : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ) (split-++ʳ Γm s') s)
    (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C) (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ C ⟧ᵗ)
      (eval (sub-match𝟙ʳ v q P Q g))
      (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (⟦split⟧ s) (eval (match𝟙 {Γ = Γm} {Δ = Δm} P Q))) (eval g))

eval-sp-sub-cons : ∀ (Χ : List M.Obₘ) {A As' w}
    (f : M.Homₘ (Χ ++ map φ.F₀ (A ∷ As')) w)
    {x Θ Γ₁ Δ₁ Ξ Γ} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
    (v : Split-++ Γ₁ Δ₁ s) (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As') (g : Tm Γ x)
  → PathP (λ i → M.Homₘ (pre-bound Χ Θ Γ Ξ i) w)
      (eval-sp Χ f (sub-cons v t ts g))
      (M._∘ₘ_ {Θ = Χ ++ ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
        (castₘ (pre-split Χ (⟦split⟧ s)) (eval-sp Χ f (t ∷ ts))) (eval g))

eval-sub s var g = eval-sub-var s g
eval-sub s (gen f' sp) g = eval-sp-sub [] (φ.F₁ f') s sp g
eval-sub s (⦅_,_⦆ {Γ = Γ₁} P Q) g = eval-sub-pair (split-++ Γ₁ s) P Q g
eval-sub s (match⊗ {Γ = Γm} P Q) g = eval-sub-match⊗ˡ (split-++ Γm s) P Q g
eval-sub s ⋆ g = absurd (split-[] s)
eval-sub s (match𝟙 {Γ = Γm} P Q) g = eval-sub-match𝟙ˡ (split-++ Γm s) P Q g

eval-sp-sub Χ f s [] g = absurd (split-[] s)
eval-sp-sub Χ f s (_∷_ {Γ = Γ₁} t ts) g =
  eval-sp-sub-cons Χ f (split-++ Γ₁ s) t ts g

eval-sub-pair (on-left s₁ p co) P Q g =
  core-pair-left s₁ p co P Q g (eval-sub s₁ P g)
eval-sub-pair (on-right s₂ q co) P Q g =
  core-pair-right s₂ q co P Q g (eval-sub s₂ Q g)

eval-sub-match⊗ˡ {A = A} {B = B} {Δm = Δm} (on-left s₁ p co) P Q g =
  core-match⊗-ˡL s₁ p co P Q g (eval-sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g)
eval-sub-match⊗ˡ {Ψ = Ψ} (on-right s' q co) P Q g =
  eval-sub-match⊗ʳ (split-++ Ψ s') q co P Q g

eval-sub-match⊗ʳ (on-left s₁ p co') q co P Q g =
  core-match⊗-ʳL s₁ p q co' co P Q g (eval-sub s₁ P g)
eval-sub-match⊗ʳ {A = A} {B = B} {Γm = Γm} (on-right s₂ q₂ co₂) q co P Q g =
  core-match⊗-ʳR s₂ q₂ q co₂ co P Q g
    (eval-sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q g)

eval-sub-match𝟙ˡ {Δm = Δm} (on-left s₁ p co) P Q g =
  core-match𝟙-ˡL s₁ p co P Q g (eval-sub (split-++ˡ s₁ Δm) Q g)
eval-sub-match𝟙ˡ {Ψ = Ψ} (on-right s' q co) P Q g =
  eval-sub-match𝟙ʳ (split-++ Ψ s') q co P Q g

eval-sub-match𝟙ʳ (on-left s₁ p co') q co P Q g =
  core-match𝟙-ʳL s₁ p q co' co P Q g (eval-sub s₁ P g)
eval-sub-match𝟙ʳ {Γm = Γm} (on-right s₂ q₂ co₂) q co P Q g =
  core-match𝟙-ʳR s₂ q₂ q co₂ co P Q g (eval-sub (split-++ʳ Γm s₂) Q g)

eval-sp-sub-cons Χ f (on-left s₁ p co) t ts g =
  core-cons-left Χ f s₁ p co t ts g (eval-sub s₁ t g)
eval-sp-sub-cons Χ f {Γ₁ = Γ₁} (on-right s₂ q co) t ts g =
  core-cons-right Χ f s₂ q co t ts g
    (eval-sp-sub (Χ ++ ⟦ Γ₁ ⟧ᶜ)
      (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ _)))
        (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ _} f (eval t)))
      s₂ ts g)

-- ==========================================================================
-- TIER 2 preliminaries: path lemmas for the β/η cases.
-- ==========================================================================

-- ⟦⟧-++₂ with empty middle is the binary homomorphism path (both
-- cons-by-cons with the same base).
⟦⟧-++₂-nil : ∀ (Γm Δm : Ctx) → ⟦⟧-++₂ Γm [] Δm ≡ ⟦⟧-++ Γm Δm
⟦⟧-++₂-nil []       Δm = refl
⟦⟧-++₂-nil (A ∷ Γm) Δm = ap (ap (⟦ A ⟧ᵗ ∷_)) (⟦⟧-++₂-nil Γm Δm)

-- The interpreted canonical split is the homomorphism path at a cons.
⟦split⟧-here : ∀ (Θ' : Ctx) (x' : Ty) (Ξ' : Ctx)
             → ⟦split⟧ (split-here Θ' x' Ξ') ≡ ⟦⟧-++ Θ' (x' ∷ Ξ')
⟦split⟧-here []       x' Ξ' = refl
⟦split⟧-here (A ∷ Θ') x' Ξ' = ap (ap (⟦ A ⟧ᵗ ∷_)) (⟦split⟧-here Θ' x' Ξ')

-- The evaluated pairing of two variables is the chosen binary arrow.
eval-pairvar : ∀ (A B : Ty)
             → eval (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)
             ≡ uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])
eval-pairvar A B =
    transport-refl _
  ∙ M.idₘl {Θ = ⟦ A ⟧ᵗ ∷ []} {Ξ = []}
      (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])) M.idₘ)
  ∙ M.idₘl {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []))

private
  sq-stepᵣ₃ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) {a b c d : X}
              (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) {u : a ≡ d}
            → p ∙ (q ∙ r) ≡ u
            → ap f p ∙ (ap f q ∙ ap f r) ≡ ap f u
  sq-stepᵣ₃ f p q r eq = ∙-ap₃ f p q r ∙ ap (ap f) eq

  -- Two-sided cons step: LHS a 2-chain, RHS a right-nested 4-chain.
  sq-step₂₄ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
              {a b c d e e' : X}
              (p : a ≡ b) (q : b ≡ c) (r : a ≡ d) (s : d ≡ e) (t : e ≡ e')
              (u : e' ≡ c)
            → p ∙ q ≡ r ∙ (s ∙ (t ∙ u))
            → ap f p ∙ ap f q ≡ ap f r ∙ (ap f s ∙ (ap f t ∙ ap f u))
  sq-step₂₄ f p q r s t u eq =
    ∙-ap₂' f p q ∙ ap (ap f) eq ∙ sym (∙-ap₄ f r s t u)

  -- β⊗: the two inner casts of the pattern's evaluation agree over ++-idr.
  sq-βP : ∀ (Γm : Ctx) (A B : Ty) (Δm : Ctx)
    → sym (⟦split⟧ (split-here Γm A (B ∷ Δm)))
      ∙ (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm
      ∙ slot-unbury ⟦ Γm ⟧ᶜ [] ⟦ A ⟧ᵗ (⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ)
    ≡ ap (_++ ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ ⟦ Δm ⟧ᶜ) (sym (++-idr ⟦ Γm ⟧ᶜ))
  sq-βP []        A B Δm = ∙-idl _ ∙ ∙-idl refl
  sq-βP (A' ∷ Γm) A B Δm =
    sq-stepᵣ₃ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦split⟧ (split-here Γm A (B ∷ Δm))))
      (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm)
      (slot-unbury ⟦ Γm ⟧ᶜ [] ⟦ A ⟧ᵗ (⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ)
      (sq-βP Γm A B Δm)

  -- β⊗: the middle bridge square (Γm-induction, base by ⟦split⟧-here).
  sq-βmid : ∀ (Γm Γ₁ : Ctx) (A B : Ty) (Δ₁ Δm : Ctx)
    → sym (⟦split⟧ (split-++ʳ Γm (split-here Γ₁ B Δm)))
      ∙ (⟦⟧-++₂ Γm Γ₁ (B ∷ Δm)
      ∙ (ap (λ l → l ++ ⟦ Γ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ ⟦ Δm ⟧ᶜ) (sym (++-idr ⟦ Γm ⟧ᶜ))
      ∙ (assocₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Γ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ
      ∙ slot-unbury ⟦ Γm ⟧ᶜ ⟦ Γ₁ ⟧ᶜ ⟦ B ⟧ᵗ [] ⟦ Δm ⟧ᶜ)))
    ≡ ap (λ l → l ++ ⟦ B ⟧ᵗ ∷ ⟦ Δm ⟧ᶜ) (⟦⟧-++ Γm Γ₁)
  sq-βmid [] Γ₁ A B Δ₁ Δm =
      ap (sym (⟦split⟧ (split-here Γ₁ B Δm)) ∙_)
        ( ap (⟦⟧-++ Γ₁ (B ∷ Δm) ∙_)
            (∙-idl _ ∙ ∙-invl (++-assoc ⟦ Γ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ))
        ∙ ∙-idr (⟦⟧-++ Γ₁ (B ∷ Δm)) )
    ∙ ap (λ z' → sym z' ∙ ⟦⟧-++ Γ₁ (B ∷ Δm)) (⟦split⟧-here Γ₁ B Δm)
    ∙ ∙-invl (⟦⟧-++ Γ₁ (B ∷ Δm))
  sq-βmid (A' ∷ Γm) Γ₁ A B Δ₁ Δm =
    sq-stepᵣ₅ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦split⟧ (split-++ʳ Γm (split-here Γ₁ B Δm))))
      (⟦⟧-++₂ Γm Γ₁ (B ∷ Δm))
      (ap (λ l → l ++ ⟦ Γ₁ ⟧ᶜ ++ ⟦ B ⟧ᵗ ∷ ⟦ Δm ⟧ᶜ) (sym (++-idr ⟦ Γm ⟧ᶜ)))
      (assocₘ-boundary ⟦ Γm ⟧ᶜ [] ⟦ Γ₁ ⟧ᶜ (⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ)
      (slot-unbury ⟦ Γm ⟧ᶜ ⟦ Γ₁ ⟧ᶜ ⟦ B ⟧ᵗ [] ⟦ Δm ⟧ᶜ)
      (sq-βmid Γm Γ₁ A B Δ₁ Δm)

  -- β⊗: the total square (a loop, decomposed two-sided; Γm then Γ₁).
  sq-βtot : ∀ (Γm Γ₁ Δ₁ Δm : Ctx)
    → sym (⟦⟧-++₂ (Γm ++ Γ₁) Δ₁ Δm) ∙ ap ⟦_⟧ᶜ (β⊗-boundary Γm Γ₁ Δ₁ Δm)
    ≡ ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++ Γm Γ₁)
      ∙ (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Γ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ
      ∙ (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (pair-path Γ₁ Δ₁)
      ∙ sym (⟦⟧-++₂ Γm (Γ₁ ++ Δ₁) Δm)))
  sq-βtot (A' ∷ Γm) Γ₁ Δ₁ Δm =
    sq-step₂₄ (⟦ A' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ (Γm ++ Γ₁) Δ₁ Δm))
      (ap ⟦_⟧ᶜ (β⊗-boundary Γm Γ₁ Δ₁ Δm))
      (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++ Γm Γ₁))
      (assocₘ-boundary ⟦ Γm ⟧ᶜ ⟦ Γ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ)
      (ap (λ l → ⟦ Γm ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (pair-path Γ₁ Δ₁))
      (sym (⟦⟧-++₂ Γm (Γ₁ ++ Δ₁) Δm))
      (sq-βtot Γm Γ₁ Δ₁ Δm)
  sq-βtot [] (B' ∷ Γ₁) Δ₁ Δm =
    sq-step₂₄ (⟦ B' ⟧ᵗ ∷_)
      (sym (⟦⟧-++₂ Γ₁ Δ₁ Δm))
      (ap ⟦_⟧ᶜ (β⊗-boundary [] Γ₁ Δ₁ Δm))
      (ap (λ l → l ++ ⟦ Δ₁ ⟧ᶜ ++ ⟦ Δm ⟧ᶜ) (⟦⟧-++ [] Γ₁))
      (assocₘ-boundary ⟦ [] ⟧ᶜ ⟦ Γ₁ ⟧ᶜ ⟦ Δ₁ ⟧ᶜ [] ⟦ Δm ⟧ᶜ)
      (ap (λ l → ⟦ [] ⟧ᶜ ++ l ++ ⟦ Δm ⟧ᶜ) (pair-path Γ₁ Δ₁))
      (sym (⟦⟧-++₂ [] (Γ₁ ++ Δ₁) Δm))
      (sq-βtot [] Γ₁ Δ₁ Δm)
  sq-βtot [] [] Δ₁ Δm =
      ∙-idr (sym (⟦⟧-++ Δ₁ Δm))
    ∙ sym ( ∙-idl _
          ∙ ap (_∙ (ap (λ l → l ++ ⟦ Δm ⟧ᶜ) (++-idr ⟦ Δ₁ ⟧ᶜ) ∙ sym (⟦⟧-++ Δ₁ Δm)))
               (ap sym (++-assoc-nil ⟦ Δ₁ ⟧ᶜ ⟦ Δm ⟧ᶜ))
          ∙ ∙-cancell (ap (λ l → l ++ ⟦ Δm ⟧ᶜ) (++-idr ⟦ Δ₁ ⟧ᶜ)) (sym (⟦⟧-++ Δ₁ Δm)) )

-- ==========================================================================
-- TIER 2: eval respects the β/η congruence.  Congruence cases are eval's
-- clauses applied under the interval; β/η go to the unit/counit of the
-- universality equivalence, bridged by Tier 1 instances.
-- ==========================================================================

eval-≈ : ∀ {Γ z} {t t' : Tm Γ z} → t ≈ t' → eval t ≡ eval t'
eval-≈ₛ : ∀ {Γ} {As : List G.Ob} (Χ : List M.Obₘ) {w}
          (f : M.Homₘ (Χ ++ map φ.F₀ As) w) {ts ts' : Sp Γ As}
        → ts ≈ₛ ts' → eval-sp Χ f ts ≡ eval-sp Χ f ts'

eval-≈ ≈-refl = refl
eval-≈ (≈-sym e) = sym (eval-≈ e)
eval-≈ (≈-trans e₁ e₂) = eval-≈ e₁ ∙ eval-≈ e₂
eval-≈ (gen-cong {f = f'} e) = eval-≈ₛ [] (φ.F₁ f') e
eval-≈ (⦅,⦆-cong {Γ = Γ₁} {A = A} {Δ = Δ₁} {B = B} e₁ e₂) i =
  castₘ (pair-path Γ₁ Δ₁)
    (M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []}
      (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []}
        (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])) (eval-≈ e₁ i))
      (eval-≈ e₂ i))
eval-≈ (match⊗-cong {Ψ = Ψ} {A = A} {B = B} {Γ = Γm} {Δ = Δm} e₁ e₂) i =
  castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
    (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
      (unplug ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ
        (castₘ (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm) (eval-≈ e₂ i)))
      (eval-≈ e₁ i))
eval-≈ (match𝟙-cong {Ψ = Ψ} {Γ = Γm} {Δ = Δm} e₁ e₂) i =
  castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
    (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
      (unplug ⟦ Γm ⟧ᶜ [] ⟦ Δm ⟧ᶜ (castₘ (⟦⟧-++ Γm Δm) (eval-≈ e₂ i)))
      (eval-≈ e₁ i))
eval-≈ (β𝟙 {C = C} {Γm = Γm} {Δm = Δm} N) =
    ap (castₘ (sym (⟦⟧-++₂ Γm [] Δm)))
       (equiv→counit (uM-universal [] {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} {z = ⟦ C ⟧ᵗ})
         (castₘ (⟦⟧-++ Γm Δm) (eval N)))
  ∙ ap (λ ρ → castₘ (sym ρ) (castₘ (⟦⟧-++ Γm Δm) (eval N))) (⟦⟧-++₂-nil Γm Δm)
  ∙ transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) (⟦⟧-++ Γm Δm)) (eval N)
eval-≈ (η𝟙 {Ψ = Ψ} {C = C} {Γm = Γm} {Δm = Δm} M N) =
    ap (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm)))
       ( ap (λ f' → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
                (unplug ⟦ Γm ⟧ᶜ [] ⟦ Δm ⟧ᶜ f') (eval M))
            ( ap (λ ρ → castₘ ρ (eval (sub (split-here Γm 𝟙 Δm) N ⋆)))
                 (sym (⟦⟧-++₂-nil Γm Δm))
            ∙ from-pathp (eval-sub (split-here Γm 𝟙 Δm) N ⋆) )
       ∙ ap (λ f' → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} f' (eval M))
            (equiv→unit (uM-universal [] {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} {z = ⟦ C ⟧ᵗ})
              (castₘ (⟦split⟧ (split-here Γm 𝟙 Δm)) (eval N)))
       ∙ sym (from-pathp (eval-sub (split-here Γm 𝟙 Δm) N M)) )
  ∙ transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) (⟦⟧-++₂ Γm Ψ Δm))
      (eval (sub (split-here Γm 𝟙 Δm) N M))
eval-≈ (η⊗ {Ψ = Ψ} {A = A} {B = B} {C = C} {Γm = Γm} {Δm = Δm} M N) =
    ap (castₘ (sym (⟦⟧-++₂ Γm Ψ Δm)))
       ( ap (λ f' → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
                (unplug ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ f') (eval M))
            (from-pathp (eval-sub (split-here Γm (A ⊗ B) Δm) N ⦅ var , var ⦆))
       ∙ ap (λ f' → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
                (unplug ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ
                  (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
                    (castₘ (⟦split⟧ (split-here Γm (A ⊗ B) Δm)) (eval N)) f'))
                (eval M))
            (eval-pairvar A B)
       ∙ ap (λ f' → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} f' (eval M))
            (equiv→unit
              (uM-universal (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])
                {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} {z = ⟦ C ⟧ᵗ})
              (castₘ (⟦split⟧ (split-here Γm (A ⊗ B) Δm)) (eval N)))
       ∙ sym (from-pathp (eval-sub (split-here Γm (A ⊗ B) Δm) N M)) )
  ∙ transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) (⟦⟧-++₂ Γm Ψ Δm))
      (eval (sub (split-here Γm (A ⊗ B) Δm) N M))
eval-≈ (β⊗ {A = A} {B = B} {C = C} {Γm = Γm} {Δm = Δm} {Γ₁ = Γ₁} {Δ₁ = Δ₁} M N P) =
  l-chain ∙ sym bridge ∙ sym r-chain
  where
    ABm GM DC C1 D1 : List M.Obₘ
    ABm = ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []
    GM = ⟦ Γm ⟧ᶜ
    DC = ⟦ Δm ⟧ᶜ
    C1 = ⟦ Γ₁ ⟧ᶜ
    D1 = ⟦ Δ₁ ⟧ᶜ

    K : M.Homₘ (GM ++ ABm ++ DC) ⟦ C ⟧ᵗ
    K = castₘ (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm) (eval P)

    UP : M.Homₘ (GM ++ ⊗M ABm ∷ DC) ⟦ C ⟧ᵗ
    UP = unplug GM ABm DC K

    W1 : M.Homₘ (C1 ++ ⟦ B ⟧ᵗ ∷ []) ⟦ A ⊗ B ⟧ᵗ
    W1 = M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} (uM ABm) (eval M)

    W2 : M.Homₘ (C1 ++ D1 ++ []) ⟦ A ⊗ B ⟧ᵗ
    W2 = M._∘ₘ_ {Θ = C1} {Ξ = []} W1 (eval N)

    su1 = slot-unbury GM C1 ⟦ B ⟧ᵗ [] DC
    bd1 = assocₘ-boundary GM C1 D1 [] DC
    su2 = slot-unbury GM [] ⟦ A ⟧ᵗ (⟦ B ⟧ᵗ ∷ []) DC
    bd2 = assocₘ-boundary GM [] C1 (⟦ B ⟧ᵗ ∷ []) DC

    s1' : Split A Γm (Γm ++ A ∷ B ∷ Δm) (B ∷ Δm)
    s1' = split-here Γm A (B ∷ Δm)

    s2' : Split B (Γm ++ Γ₁) (Γm ++ Γ₁ ++ B ∷ Δm) Δm
    s2' = split-++ʳ Γm (split-here Γ₁ B Δm)

    E1 = ⟦⟧-++₂ Γm (Γ₁ ++ Δ₁) Δm
    E2 = ⟦⟧-++₂ (Γm ++ Γ₁) Δ₁ Δm
    E3 = ⟦⟧-++₂ Γm Γ₁ (B ∷ Δm)
    bb = β⊗-boundary Γm Γ₁ Δ₁ Δm
    app1 = ap (λ l → GM ++ l ++ DC) (pair-path Γ₁ Δ₁)

    YR : M.Homₘ (GM ++ C1 ++ ⟦ B ∷ Δm ⟧ᶜ) ⟦ C ⟧ᵗ
    YR = M._∘ₘ_ {Θ = GM} {Ξ = ⟦ B ∷ Δm ⟧ᶜ} (castₘ (⟦split⟧ s1') (eval P)) (eval M)

    YL : M.Homₘ ((GM ++ []) ++ C1 ++ (⟦ B ⟧ᵗ ∷ []) ++ DC) ⟦ C ⟧ᵗ
    YL = M._∘ₘ_ {Θ = GM ++ []} {Ξ = (⟦ B ⟧ᵗ ∷ []) ++ DC} (castₘ su2 K) (eval M)

    coreL : M.Homₘ ((GM ++ C1) ++ D1 ++ ([] ++ DC)) ⟦ C ⟧ᵗ
    coreL = M._∘ₘ_ {Θ = GM ++ C1} {Ξ = [] ++ DC}
              (castₘ su1 (castₘ bd2 YL)) (eval N)

    coreR : M.Homₘ (⟦ Γm ++ Γ₁ ⟧ᶜ ++ D1 ++ DC) ⟦ C ⟧ᵗ
    coreR = M._∘ₘ_ {Θ = ⟦ Γm ++ Γ₁ ⟧ᶜ} {Ξ = DC}
              (castₘ (⟦split⟧ s2') (castₘ (sym E3) YR)) (eval N)

    l-chain : eval (match⊗ {Γ = Γm} {Δ = Δm} ⦅ M , N ⦆ P)
            ≡ castₘ (sym E1) (castₘ app1 (castₘ bd1 coreL))
    l-chain = ap (castₘ (sym E1))
        ( sym (from-pathp (λ i → M._∘ₘ_ {Θ = GM} {Ξ = DC} UP
                  (castₘ-filler (pair-path Γ₁ Δ₁) W2 i)))
        ∙ ap (castₘ app1)
            ( sym (from-pathp (M.assocₘ {Θ = GM} {Ξ = DC} {Φ = C1} {Ψ = []}
                     {Ρ = D1} UP W1 (eval N)))
            ∙ ap (castₘ bd1)
                (ap (λ h → M._∘ₘ_ {Θ = GM ++ C1} {Ξ = [] ++ DC}
                       (castₘ su1 h) (eval N))
                   ( sym (from-pathp (M.assocₘ {Θ = GM} {Ξ = DC} {Φ = []}
                            {Ψ = ⟦ B ⟧ᵗ ∷ []} {Ρ = C1} UP (uM ABm) (eval M)))
                   ∙ ap (λ h' → castₘ bd2
                            (M._∘ₘ_ {Θ = GM ++ []} {Ξ = (⟦ B ⟧ᵗ ∷ []) ++ DC}
                              (castₘ su2 h') (eval M)))
                        (equiv→counit
                          (uM-universal ABm {Θ = GM} {Ξ = DC} {z = ⟦ C ⟧ᵗ}) K) )) ) )

    r-chain : eval (cast bb (sub s2' (sub s1' P M) N))
            ≡ castₘ (ap ⟦_⟧ᶜ bb) (castₘ (sym E2) coreR)
    r-chain =
        sym (from-pathp (eval-cast bb (sub s2' (sub s1' P M) N)))
      ∙ ap (castₘ (ap ⟦_⟧ᶜ bb))
          ( sym (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) E2) (eval (sub s2' (sub s1' P M) N)))
          ∙ ap (castₘ (sym E2)) (from-pathp (eval-sub s2' (sub s1' P M) N))
          ∙ ap (castₘ (sym E2))
              (ap (λ h → M._∘ₘ_ {Θ = ⟦ Γm ++ Γ₁ ⟧ᶜ} {Ξ = DC}
                     (castₘ (⟦split⟧ s2') h) (eval N))
                 ( sym (transport⁻transport (ap (Homf ⟦ C ⟧ᵗ) E3) (eval (sub s1' P M)))
                 ∙ ap (castₘ (sym E3)) (from-pathp (eval-sub s1' P M)) )) )

    PB : PathP (λ k → M.Homₘ (++-idr GM (~ k) ++ ⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ DC) ⟦ C ⟧ᵗ)
           (castₘ (⟦split⟧ s1') (eval P))
           (castₘ su2 K)
    PB = hom-over (sq-βP Γm A B Δm)
           (hom-∙P (symP (castₘ-filler (⟦split⟧ s1') (eval P)))
           (hom-∙P (castₘ-filler (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm) (eval P))
                   (castₘ-filler su2 K)))

    BBin : PathP (λ k → M.Homₘ (⟦⟧-++ Γm Γ₁ k ++ ⟦ B ⟧ᵗ ∷ DC) ⟦ C ⟧ᵗ)
             (castₘ (⟦split⟧ s2') (castₘ (sym E3) YR))
             (castₘ su1 (castₘ bd2 YL))
    BBin = hom-over (sq-βmid Γm Γ₁ A B Δ₁ Δm)
             (hom-∙P (symP (castₘ-filler (⟦split⟧ s2') (castₘ (sym E3) YR)))
             (hom-∙P (symP (castₘ-filler (sym E3) YR))
             (hom-∙P (λ k → M._∘ₘ_ {Θ = ++-idr GM (~ k)} {Ξ = ⟦ B ⟧ᵗ ∷ DC}
                        (PB k) (eval M))
             (hom-∙P (castₘ-filler bd2 YL)
                     (castₘ-filler su1 (castₘ bd2 YL))))))

    sq-βloop : sym (ap ⟦_⟧ᶜ bb)
               ∙ (E2
               ∙ (ap (λ l → l ++ D1 ++ DC) (⟦⟧-++ Γm Γ₁)
               ∙ (bd1 ∙ (app1 ∙ sym E1))))
             ≡ refl
    sq-βloop =
        ap (λ z' → sym (ap ⟦_⟧ᶜ bb) ∙ (E2 ∙ z')) (sym (sq-βtot Γm Γ₁ Δ₁ Δm))
      ∙ ap (sym (ap ⟦_⟧ᶜ bb) ∙_) (∙-cancell (sym E2) (ap ⟦_⟧ᶜ bb))
      ∙ ∙-invl (ap ⟦_⟧ᶜ bb)

    bridge : castₘ (ap ⟦_⟧ᶜ bb) (castₘ (sym E2) coreR)
           ≡ castₘ (sym E1) (castₘ app1 (castₘ bd1 coreL))
    bridge = hom-over sq-βloop
        (hom-∙P (symP (castₘ-filler (ap ⟦_⟧ᶜ bb) (castₘ (sym E2) coreR)))
        (hom-∙P (symP (castₘ-filler (sym E2) coreR))
        (hom-∙P (λ k → M._∘ₘ_ {Θ = ⟦⟧-++ Γm Γ₁ k} {Ξ = DC} (BBin k) (eval N))
        (hom-∙P (castₘ-filler bd1 coreL)
        (hom-∙P (castₘ-filler app1 (castₘ bd1 coreL))
                (castₘ-filler (sym E1) (castₘ app1 (castₘ bd1 coreL))))))))

eval-≈ₛ Χ f nil = refl
eval-≈ₛ Χ f (cons {Γ = Γ₁} {Δ = Δ₁} {As = As'} {A = A} {t = t} {t' = t'}
             {ts = ts} {ts' = ts'} e es) =
  ap (castₘ (sp-step-path Χ Γ₁ Δ₁))
     ( (λ i → eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ)
          (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ As')))
            (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ As'} f (eval-≈ e i)))
          ts)
     ∙ eval-≈ₛ (Χ ++ ⟦ Γ₁ ⟧ᶜ)
         (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ As')))
           (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ As'} f (eval t')))
         es )

-- ==========================================================================
-- TIER 3: descent to the syntactic multicategory and packaging as a
-- multifunctor FMonCat G → M (the freeness map of Theorem 2.4.10).
-- ==========================================================================

open import Data.Set.Coequaliser using (Quot-elim ; Coeq-elim-prop ; inc)
open import Multicategory.Functor using (Multifunctor)
open import Multicategory.Free.Multicategory G
  using (Homᶠ ; idᶠ ; _∘ᶠ_ ; FMonCat)

evalᶠ : ∀ {Γ z} → Homᶠ Γ z → M.Homₘ ⟦ Γ ⟧ᶜ ⟦ z ⟧ᵗ
evalᶠ = Quot-elim (λ _ → M.Homₘ-set) eval (λ t t' r → eval-≈ r)

Eval-multifunctor : Multifunctor FMonCat M
Eval-multifunctor .Multifunctor.F₀ = ⟦_⟧ᵗ
Eval-multifunctor .Multifunctor.F₁ = evalᶠ
Eval-multifunctor .Multifunctor.F-idₘ = refl
Eval-multifunctor .Multifunctor.F-∘ₘ {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {x = x} {z = z} =
  Coeq-elim-prop
    (λ f → Π-is-hlevel 1 λ g →
       PathP-is-hlevel' 1 M.Homₘ-set
         (evalᶠ (M'._∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g))
         (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
           (castₘ (⟦⟧-++ Θ (x ∷ Ξ)) (evalᶠ f)) (evalᶠ g)))
    (λ t → Coeq-elim-prop
      (λ g → PathP-is-hlevel' 1 M.Homₘ-set
         (evalᶠ (M'._∘ₘ_ {Θ = Θ} {Ξ = Ξ} (inc t) g))
         (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
           (castₘ (⟦⟧-++ Θ (x ∷ Ξ)) (eval t)) (evalᶠ g)))
      (λ u → eval-sub (split-here Θ x Ξ) t u
             ▷ ap (λ ρ → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                     (castₘ ρ (eval t)) (eval u))
                  (⟦split⟧-here Θ x Ξ)))
  where
    module M' = Premulticategory FMonCat
