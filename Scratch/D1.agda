module Scratch.D1 where

-- D3 experiment: tri← in Coherence.agda is exactly 1lab's `triangle-inv`
-- (Cat.Bi.Reasoning, instantiated at Deloop M₀), and the hand-rolled
-- unitor-naturality steps are MR.ρ→nat / MR.λ→nat (already exported by
-- Cat.Monoidal.Reasoning, which Coherence imports as MR).

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base
import Cat.Reasoning as Cr
import Cat.Monoidal.Reasoning as MonR
import Cat.Bi.Reasoning
open import Data.List using (List; []; _∷_; _++_)

open import Multicategory.Instances.Monoidal

module _ {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using (⊗-context ; plug ; plug-nil ; ⊗-context-++ ; ⊗-context-++-[]-ρ)

  private module MR = MonR M₀
  open Cat.Bi.Reasoning (Deloop M₀) using (triangle-inv)

  -- The 20-line tri← is a 1lab one-liner.
  tri←' : (a x : Ob) → α← (a , Unit , x) ∘ (a ▶ λ→ x) ≡ ρ→ a ◀ x
  tri←' a x = triangle-inv {f = a} {g = x}

  -- plug-sing with MR.ρ→nat instead of raw `unitor-r.to .is-natural`,
  -- and ▶.intror instead of the idr/F-id dance.
  plug-sing' : (a b : Ob) (m : Hom (a ⊗ Unit) b)
    → plug [] (a ∷ []) [] m ≡ ρ→ b ∘ m
  plug-sing' a b m =
      plug-nil (a ∷ []) [] m
    ∙ ap ((m ◀ Unit) ∘_) (▶.intror refl ∙ ⊗-context-++-[]-ρ (a ∷ []))
    ∙ sym (MR.ρ→nat m)
