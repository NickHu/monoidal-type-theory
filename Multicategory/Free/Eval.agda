open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory
open import Multicategory.Free
open import Multicategory.Functor using (map-++₂)
import Multicategory.Representable as Rep

-- Evaluation of the simple type theory of Multicategory.Free into an
-- arbitrary representable premulticategory M: the map underlying the
-- freeness theorem (Shulman, Theorem 2.4.10).  Definitions only; the laws
-- (eval maps sub to _∘ₘ_, eval respects _≈_, descent to Homₘ) are proved in
-- Free/Freeness, and uniqueness in Free/Uniqueness.
--
-- Transport discipline (as everywhere in this development): every context
-- reconciliation is a NAMED structural path, cons-by-cons or a definitional
-- alias of a structural 1lab lemma — never an inline ∙-chain — so that the
-- law proofs can reason through them.

module Multicategory.Free.Eval
  {o h o' h'} (G : Multigraph o h)
  (M : Premulticategory o' h') (rep : Rep.is-representable M)
  where

open Syntax G

private
  module G = Multigraph G
  module M = Premulticategory M

-- M's chosen tensors and universal arrows.
⊗M : List M.Obₘ → M.Obₘ
⊗M = Rep.⊗ M rep

uM : (Γ : List M.Obₘ) → M.Homₘ Γ (⊗M Γ)
uM = Rep.⊗-arr M rep

uM-universal : (Γ : List M.Obₘ) → Rep.is-universal M (uM Γ)
uM-universal = Rep.⊗-arr-universal M rep

-- Transport a multimorphism of M along a context path (the M-side analogue
-- of Syntax.cast).
castₘ : {Ω Ω' : List M.Obₘ} {z : M.Obₘ} → Ω ≡ Ω' → M.Homₘ Ω z → M.Homₘ Ω' z
castₘ {z = z} p = subst (λ Ω → M.Homₘ Ω z) p

-- The inverse of the universality equivalence (- ∘ₘ uM Υ) at slot Θ | Ξ:
-- turn a map out of Θ ++ Υ ++ Ξ into a map out of Θ ++ ⊗M Υ ∷ Ξ.  Υ is
-- explicit because Agda cannot invert _++_ to recover it (in the nullary
-- case Θ ++ [] ++ Ξ even reduces away).
unplug : (Θ Υ Ξ : List M.Obₘ) {z : M.Obₘ}
       → M.Homₘ (Θ ++ Υ ++ Ξ) z → M.Homₘ (Θ ++ ⊗M Υ ∷ Ξ) z
unplug Θ Υ Ξ {z} = equiv→inverse (uM-universal Υ {Θ = Θ} {Ξ = Ξ} {z = z})

-- A multigraph map from G into the underlying multigraph of M.
record Multigraph-hom↓ : Type (o ⊔ h ⊔ o' ⊔ h') where
  no-eta-equality
  field
    F₀ : G.Ob → M.Obₘ
    F₁ : ∀ {As : List G.Ob} {B : G.Ob}
       → G.Hom As B → M.Homₘ (map F₀ As) (F₀ B)

module _ (φ : Multigraph-hom↓) where
  private module φ = Multigraph-hom↓ φ

  -- Types are interpreted by folding through M's chosen representability.
  ⟦_⟧ᵗ : Ty → M.Obₘ
  ⟦ base b ⟧ᵗ = φ.F₀ b
  ⟦ A ⊗ B ⟧ᵗ  = ⊗M (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])
  ⟦ 𝟙 ⟧ᵗ      = ⊗M []

  ⟦_⟧ᶜ : Ctx → List M.Obₘ
  ⟦_⟧ᶜ = map ⟦_⟧ᵗ

  -- ⟦_⟧ᶜ is NOT definitionally a ++-homomorphism; these two structural
  -- paths (definitional aliases of map-++ / map-++₂, themselves
  -- cons-by-cons) mediate.
  ⟦⟧-++ : (Γ Δ : Ctx) → ⟦ Γ ++ Δ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ++ ⟦ Δ ⟧ᶜ
  ⟦⟧-++ = map-++ ⟦_⟧ᵗ

  ⟦⟧-++₂ : (Γ Ψ Δ : Ctx) → ⟦ Γ ++ Ψ ++ Δ ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ++ ⟦ Ψ ⟧ᶜ ++ ⟦ Δ ⟧ᶜ
  ⟦⟧-++₂ = map-++₂ ⟦_⟧ᵗ

  -- Boundary of the spine step: after plugging the head's evaluation and
  -- recursing with the grown prefix Χ ++ ⟦ Γ₁ ⟧ᶜ, land back on the
  -- interpreted concatenated context.  Cons-by-cons on Χ; the base case is
  -- sym (⟦⟧-++ Γ₁ Δ), still cons-headed under sym.
  sp-step-path : (Χ : List M.Obₘ) (Γ₁ Δ : Ctx)
               → (Χ ++ ⟦ Γ₁ ⟧ᶜ) ++ ⟦ Δ ⟧ᶜ ≡ Χ ++ ⟦ Γ₁ ++ Δ ⟧ᶜ
  sp-step-path []      Γ₁ Δ = sym (⟦⟧-++ Γ₁ Δ)
  sp-step-path (a ∷ Χ) Γ₁ Δ = ap (a ∷_) (sp-step-path Χ Γ₁ Δ)

  -- Boundary of the pair case: absorb the trailing [] left by _∘ₘ_ at
  -- Ξ = [] and fuse the two interpreted contexts.  Cons-by-cons on Γ₁;
  -- the base case is 1lab's structural ++-idr.
  pair-path : (Γ₁ Δ₁ : Ctx) → ⟦ Γ₁ ⟧ᶜ ++ ⟦ Δ₁ ⟧ᶜ ++ [] ≡ ⟦ Γ₁ ++ Δ₁ ⟧ᶜ
  pair-path []       Δ₁ = ++-idr ⟦ Δ₁ ⟧ᶜ
  pair-path (a ∷ Γ₁) Δ₁ = ap (⟦ a ⟧ᵗ ∷_) (pair-path Γ₁ Δ₁)

  -- ==========================================================================
  -- Evaluation, mutually on terms and spines.  eval-sp generalises over the
  -- already-consumed prefix Χ: it plugs the spine's evaluations one after
  -- another into the remaining generator slots (map φ.F₀ As).
  -- ==========================================================================

  eval : ∀ {Γ : Ctx} {z : Ty} → Tm Γ z → M.Homₘ ⟦ Γ ⟧ᶜ ⟦ z ⟧ᵗ
  eval-sp : ∀ {As : List G.Ob} {Δ : Ctx} {w : M.Obₘ} (Χ : List M.Obₘ)
          → M.Homₘ (Χ ++ map φ.F₀ As) w → Sp Δ As → M.Homₘ (Χ ++ ⟦ Δ ⟧ᶜ) w

  -- var: ⟦ A ∷ [] ⟧ᶜ is definitionally ⟦ A ⟧ᵗ ∷ [].
  eval var = M.idₘ

  -- gen: [] ++ - is definitional, so no leading cleanup.
  eval (gen f sp) = eval-sp [] (φ.F₁ f) sp

  -- ⦅P,Q⦆: plug eval P into the first slot of the binary universal arrow
  -- (Θ = [], contexts agree definitionally), then eval Q into the second
  -- (Ξ = [], leaving a trailing [] absorbed by pair-path).
  eval (⦅_,_⦆ {Γ = Γ₁} {A = A} {Δ = Δ₁} {B = B} P Q) =
    castₘ (pair-path Γ₁ Δ₁)
      (M._∘ₘ_ {Θ = ⟦ Γ₁ ⟧ᶜ} {Ξ = []}
        (M._∘ₘ_ {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []}
          (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])) (eval P))
        (eval Q))

  -- match⊗: move eval Q across ⟦⟧-++₂ (with (A ∷ B ∷ []) ++ Δm reducing
  -- definitionally), invert universality of the binary arrow, plug eval P,
  -- and come back across ⟦⟧-++₂.
  eval (match⊗ {Ψ = Ψ} {A = A} {B = B} {Γ = Γm} {Δ = Δm} P Q) =
    castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
        (unplug ⟦ Γm ⟧ᶜ (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []) ⟦ Δm ⟧ᶜ
          (castₘ (⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm) (eval Q)))
        (eval P))

  -- ⋆: contexts agree definitionally.
  eval ⋆ = uM []

  -- match𝟙: same shape with the nullary arrow; ⟦ Γm ⟧ᶜ ++ [] ++ ⟦ Δm ⟧ᶜ
  -- reduces, so the outgoing transport is just ⟦⟧-++.
  eval (match𝟙 {Ψ = Ψ} {Γ = Γm} {Δ = Δm} P Q) =
    castₘ (sym (⟦⟧-++₂ Γm Ψ Δm))
      (M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
        (unplug ⟦ Γm ⟧ᶜ [] ⟦ Δm ⟧ᶜ
          (castₘ (⟦⟧-++ Γm Δm) (eval Q)))
        (eval P))

  -- []: Χ ++ map φ.F₀ [] and Χ ++ ⟦ [] ⟧ᶜ agree definitionally.
  eval-sp Χ f [] = f

  -- t ∷ ts: plug eval t into the head slot, reassociate the grown prefix
  -- (structural ++-assoc), recurse, and land via sp-step-path.
  eval-sp Χ f (_∷_ {Γ = Γ₁} {Δ = Δ} {As = As} t ts) =
    castₘ (sp-step-path Χ Γ₁ Δ)
      (eval-sp (Χ ++ ⟦ Γ₁ ⟧ᶜ)
        (castₘ (sym (++-assoc Χ ⟦ Γ₁ ⟧ᶜ (map φ.F₀ As)))
          (M._∘ₘ_ {Θ = Χ} {Ξ = map φ.F₀ As} f (eval t)))
        ts)
