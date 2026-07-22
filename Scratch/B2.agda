module Scratch.B2 where

-- B2: the four prefix-induction proofs (plug-assoc, plug-assoc-nil,
-- plug-shift, plug-interchange) share an identical cons-step:
--   rewrite plug (b ∷ Ω) by plug-cons, merge the four ▶-factors (▶.F-∘ ×3),
--   apply the IH inside the ▶, unmerge once, slide the naturality square.
-- ONE generic combinator (cons-step, plus the n-ary whisker-distribution ▶-∘₄)
-- captures it.  Validation: plug-shift re-proved below; its cons case drops
-- from 28 lines (961-989 in Monoidal.agda) to 4.
-- plug-assoc and plug-assoc-nil have the same shape (k := α← via
-- split3-cons / the definitional ⊗-context-++ cons unfolding); plug-interchange
-- uses the k-free variant (▶-weave₄).

open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Functor.Naturality
open import Data.List
open import Data.List.Properties
import Cat.Bi.Reasoning
import Multicategory.Instances.Monoidal as MIM

module _ {o h} (C : Precategory o h) (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M
  open Cat.Bi.Reasoning (Deloop M) using (λ→nat ; ▶-assoc)
  open MIM.Repr C M using
    ( ⊗-context ; ⊗-context-++ ; plug ; plug-cons ; ic-slot₁-iso ; ic-flatten-iso
    ; ic-slot₀-iso ; ic-slot₂-iso ; ic-boundary-iso )

  -- Whisker a ▶_ distributed over a 4-composite (named once; the file inlines
  -- this ▶.F-∘ chain five times).
  ▶-∘₄ : (b : Ob) {A₀ A₁ A₂ A₃ A₄ : Ob}
    (p : Hom A₃ A₄) (q : Hom A₂ A₃) (r : Hom A₁ A₂) (s : Hom A₀ A₁)
    → b ▶ (p ∘ q ∘ r ∘ s) ≡ (b ▶ p) ∘ (b ▶ q) ∘ (b ▶ r) ∘ (b ▶ s)
  ▶-∘₄ b p q r s =
    ▶.F-∘ _ _ ∙ ap ((b ▶ p) ∘_) (▶.F-∘ _ _ ∙ ap ((b ▶ q) ∘_) (▶.F-∘ _ _))

  -- The shared cons-step: given the IH (a 4-composite equals X ∘ t) and a
  -- naturality square k ∘ (b ▶ X) ≡ X' ∘ k', conclude the whiskered form.
  cons-step : {b : Ob} {A₀ A₁ A₂ A₃ A₄ W U V : Ob}
    {s : Hom A₃ A₄} {i₁ : Hom A₂ A₃} {P : Hom A₁ A₂} {i₂ : Hom A₀ A₁}
    {X : Hom W A₄} {t : Hom A₀ W}
    {k : Hom (b ⊗ A₄) V} {k' : Hom (b ⊗ W) U} {X' : Hom U V}
    → s ∘ i₁ ∘ P ∘ i₂ ≡ X ∘ t
    → k ∘ (b ▶ X) ≡ X' ∘ k'
    → (k ∘ (b ▶ s)) ∘ (b ▶ i₁) ∘ (b ▶ P) ∘ (b ▶ i₂) ≡ X' ∘ k' ∘ (b ▶ t)
  cons-step {b = b} {s = s} {i₁} {P} {i₂} ih nat =
      sym (assoc _ _ _)
    ∙ ap (_ ∘_) (sym (▶-∘₄ b s i₁ P i₂) ∙ ap (b ▶_) ih ∙ ▶.F-∘ _ _)
    ∙ extendl nat

  -- Validation: plug-shift (lines 951-989 of Monoidal.agda, 39 lines) becomes:
  module _ (Μ : List Ob) (y : Ob) (Κ Δ : List Ob)
           (h : Hom (⊗-context Δ) y) where

    plug-shift' : (Γ' : List Ob)
      →   (⊗-context-++ Γ' (Μ ++ y ∷ Κ)) .to
            ∘ (ic-slot₁-iso [] Γ' Μ y Κ) .from
            ∘ plug (Γ' ++ Μ) Δ Κ h
            ∘ (ic-flatten-iso Γ' Μ Δ Κ) .from
        ≡   (⊗-context Γ' ▶ plug Μ Δ Κ h)
            ∘ (⊗-context-++ Γ' (Μ ++ Δ ++ Κ)) .to
    plug-shift' [] =
        ap (λ→ (⊗-context (Μ ++ y ∷ Κ)) ∘_) (idl _ ∙ idr _)
      ∙ λ→nat (plug Μ Δ Κ h)
    plug-shift' (b ∷ Γ') =
        ap (λ z → (⊗-context-++ (b ∷ Γ') (Μ ++ y ∷ Κ)) .to
                ∘ (b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from)
                ∘ z
                ∘ (b ▶ (ic-flatten-iso Γ' Μ Δ Κ) .from))
           (plug-cons b (Γ' ++ Μ) Δ Κ h)
      ∙ cons-step (plug-shift' Γ')
          ((▶-assoc {f = b} {g = ⊗-context Γ'}) .Isoⁿ.from .is-natural _ _
            (plug Μ Δ Κ h))

  -- The k-free variant, for plug-interchange's cons (all four factors are
  -- ▶-whiskered; no α← correction, no naturality square).
  ▶-weave₄ : (b : Ob) {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ : Ob}
    {p : Hom A₃ A₄} {q : Hom A₂ A₃} {r : Hom A₁ A₂} {s : Hom A₀ A₁}
    {p' : Hom B₃ A₄} {q' : Hom B₂ B₃} {r' : Hom B₁ B₂} {s' : Hom A₀ B₁}
    → p ∘ q ∘ r ∘ s ≡ p' ∘ q' ∘ r' ∘ s'
    → (b ▶ p) ∘ (b ▶ q) ∘ (b ▶ r) ∘ (b ▶ s)
    ≡ (b ▶ p') ∘ (b ▶ q') ∘ (b ▶ r') ∘ (b ▶ s')
  ▶-weave₄ b {p = p} {q} {r} {s} {p'} {q'} {r'} {s'} eq =
    sym (▶-∘₄ b p q r s) ∙ ap (b ▶_) eq ∙ ▶-∘₄ b p' q' r' s'

  -- Validation: plug-interchange's cons case (lines 1041-1085, 45 lines)
  -- becomes an 8-line step given the IH.
  module _ (Θ*  Γ Μ Δ Κ : List Ob) {x y : Ob}
           (g : Hom (⊗-context Γ) x) (h : Hom (⊗-context Δ) y) where

    private
      LHS RHS : (Θ' : List Ob) → Hom _ _
      LHS Θ' = plug Θ' Γ (Μ ++ y ∷ Κ) g
             ∘ (ic-slot₁-iso Θ' Γ Μ y Κ) .from
             ∘ plug (Θ' ++ Γ ++ Μ) Δ Κ h
             ∘ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from
      RHS Θ' = (ic-slot₀-iso Θ' x Μ y Κ) .from
             ∘ plug (Θ' ++ x ∷ Μ) Δ Κ h
             ∘ (ic-slot₂-iso Θ' x Μ Δ Κ) .from
             ∘ plug Θ' Γ (Μ ++ Δ ++ Κ) g

    plug-interchange-cons : (a : Ob) (Θ' : List Ob)
      → LHS Θ' ≡ RHS Θ' → LHS (a ∷ Θ') ≡ RHS (a ∷ Θ')
    plug-interchange-cons a Θ' ih =
        ap₂ (λ u v → u ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
                       ∘ v ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from))
            (plug-cons a Θ' Γ (Μ ++ y ∷ Κ) g)
            (plug-cons a (Θ' ++ Γ ++ Μ) Δ Κ h)
      ∙ ▶-weave₄ a ih
      ∙ ap (λ u → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
                ∘ u ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from)
                ∘ (a ▶ plug Θ' Γ (Μ ++ Δ ++ Κ) g))
           (sym (plug-cons a (Θ' ++ x ∷ Μ) Δ Κ h))
      ∙ ap (λ v → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
                ∘ plug ((a ∷ Θ') ++ x ∷ Μ) Δ Κ h
                ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from) ∘ v)
           (sym (plug-cons a Θ' Γ (Μ ++ Δ ++ Κ) g))
