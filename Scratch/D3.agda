module Scratch.D3 where

-- D2 experiment: `bundle` (120-line cons-induction in Coherence.agda) redone by
-- (1) collapsing both `plug _ _ _ id` legs with the already-proven
--     `plug-id`/`Piso` from Instances/Monoidal (imported but unused for this in
--     Coherence), so the induction never touches `plug` again; and
-- (2) running the remaining pure-iso induction with Cat.Reasoning combinators
--     (pullr/cancell) + MR.λ→nat instead of raw assoc/ap chains.
-- The statement is verbatim the original `bundle` statement (⊗₀ from Strict).

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso)
import Cat.Reasoning as Cr
import Cat.Monoidal.Reasoning as MonR
open import Data.List using (List; []; _∷_; _++_; ++-idr)

open import Multicategory
open import Multicategory.Instances.Monoidal
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Instances.Monoidal.Coherence as Coh

module _ {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using
    ( ⊗-context ; plug ; plug-id ; Piso ; ⊗-context-++ ; ⊗-context-++-idr
    ; ⊗-context-++-idr-path ; ⊗-context-++-[]-ρ ; path→iso-ap-⊗ ; φ )

  private
    Mᵣ : Premulticategory o h
    Mᵣ = monoidal→multicategory C M₀
    rep : Rep.is-representable Mᵣ
    rep = monoidal→multicategory-is-representable C M₀

  open Strict Mᵣ rep using (⊗₀)
  open Coh C M₀ using (α-mid)
  private module MR = MonR M₀

  -- The pure-iso core: no `plug` in sight, every constituent reduces
  -- definitionally at [] and ∷ (⊗-context-++, Piso, φ are structural).
  core : (Γ Δ : List Ob)
    → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
        ∘ (⊗-context-++ Γ (⊗₀ Δ ∷ [])) .to) ∘ Piso Γ Δ [] .to
      ≡ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .to
  core [] Δ =
      ap (_∘ (⊗-context-++ Δ []) .to)
         (pullr (sym (MR.λ→nat (ρ← D))) ∙ cancell (λ≅ .invr))
    ∙ ap (ρ← D ∘_)
         (intror (⊗-context-++-idr Δ .invr) ∙ pulll (⊗-context-++-[]-ρ Δ))
    ∙ cancell (ρ≅ .invr)
    ∙ ap (λ i → i .to) (sym (⊗-context-++-idr-path Δ))
    where D = ⊗-context Δ
  core (a ∷ Γ) Δ =
      ap (_∘ (a ▶ Piso Γ Δ [] .to))
         ( ap (_∘ (α← _ ∘ (a ▶ ψ .to))) (pullr (α-mid a (⊗-context Γ) (ρ← D)))
         ∙ pullr (pullr (cancell (α≅ .invl)))
         ∙ ap ((a ▶ φ Γ Δ) ∘_) (sym (▶.F-∘ _ _))
         ∙ sym (▶.F-∘ _ _) )
    ∙ sym (▶.F-∘ _ _)
    ∙ ap (a ▶_) (ap (_∘ Piso Γ Δ [] .to) (assoc _ _ _) ∙ core Γ Δ)
    ∙ ap (λ i → i .to) (sym (path→iso-ap-⊗ a (ap ⊗-context (ap (Γ ++_) (++-idr Δ)))))
    where
      D = ⊗-context Δ
      ψ = ⊗-context-++ Γ (⊗₀ Δ ∷ [])

  -- The original `bundle` statement, now two plug-id rewrites + core.
  bundle' : (Γ Δ : List Ob)
    → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
        ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id
      ≡ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .to
  bundle' Γ Δ =
      ap₂ (λ (u : Hom (⊗-context (Γ ++ ⊗₀ Δ ∷ [])) (⊗-context Γ ⊗ (⊗₀ Δ ⊗ Unit)))
             (v : Hom (⊗-context (Γ ++ Δ ++ [])) (⊗-context (Γ ++ ⊗₀ Δ ∷ [])))
           → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ))) ∘ u) ∘ v)
          (plug-id [] Γ (⊗₀ Δ ∷ [])) (plug-id Γ Δ [])
    ∙ core Γ Δ
