module Scratch.A4 where

open import 1Lab.Prelude
open import Cat.Univalent using (is-category)
open import Data.List using (List; []; _∷_; _++_; ++-assoc)

open import Multicategory
open import Multicategory.Unary

-- A4: `is-multicategory M` is definitionally `is-category (Unary M)`,
-- so Representable.agda's `module _ (cat : is-category (Unary M))`
-- could take `is-multicategory M` verbatim.
module _ {o h} (M : Premulticategory o h) where
  _ : is-multicategory M ≡ is-category (Unary M)
  _ = refl

-- Bonus (helper unification): 1lab's ++-assoc is itself structurally
-- recursive ([] ↦ refl, cons ↦ ap (x ∷_)), so three of the six hand-rolled
-- path helpers in Multicategory.agda are definitional aliases of it:
--   interchange-flatten Γ Μ Δ Κ  =  ++-assoc Γ Μ (Δ ++ Κ)
--   interchange-slot₂ Θ x Μ Δ Κ  =  ++-assoc Θ (x ∷ Μ) (Δ ++ Κ)
--   interchange-slot₀ Θ x Μ y Κ  =  sym (++-assoc Θ (x ∷ Μ) (y ∷ Κ))
-- The inductive proofs below have refl leaves in BOTH clauses, i.e. the two
-- sides agree definitionally case-by-case: replacing the definitions keeps
-- every definitional unfolding an instance relies on ([]-base and ∷-step).
module _ {ℓ} {A : Type ℓ} where

  flat≡assoc : (Γ Μ Δ Κ : List A)
    → interchange-flatten Γ Μ Δ Κ ≡ ++-assoc Γ Μ (Δ ++ Κ)
  flat≡assoc []      Μ Δ Κ = refl
  flat≡assoc (a ∷ Γ) Μ Δ Κ = ap (ap (a ∷_)) (flat≡assoc Γ Μ Δ Κ)

  slot₂≡assoc : (Θ : List A) (x : A) (Μ Δ Κ : List A)
    → interchange-slot₂ Θ x Μ Δ Κ ≡ ++-assoc Θ (x ∷ Μ) (Δ ++ Κ)
  slot₂≡assoc []      x Μ Δ Κ = refl
  slot₂≡assoc (a ∷ Θ) x Μ Δ Κ = ap (ap (a ∷_)) (slot₂≡assoc Θ x Μ Δ Κ)

  slot₀≡assoc : (Θ : List A) (x : A) (Μ : List A) (y : A) (Κ : List A)
    → interchange-slot₀ Θ x Μ y Κ ≡ sym (++-assoc Θ (x ∷ Μ) (y ∷ Κ))
  slot₀≡assoc []      x Μ y Κ = refl
  slot₀≡assoc (a ∷ Θ) x Μ y Κ = ap (ap (a ∷_)) (slot₀≡assoc Θ x Μ y Κ)
