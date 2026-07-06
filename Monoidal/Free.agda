open import Monoidal.Free.Signature
open import Cat.Prelude
open import Cat.Monoidal.Base

open import Data.Nat
open import Data.Vec.Base

module Monoidal.Free {ℓ} (S : 𝓖 ℓ) where

open 𝓖 S renaming (Ob to Node ; Hom to Edge)

Ctx : {n : Nat} → Type ℓ
Ctx {n} = Vec Ty n

data Mor : Σ[ n ∈ Nat ] Ctx {n} → Ty → Type ℓ
private variable
  τ σ ρ : Ty
  n : Nat
  Γ Ψ Δ : Ctx {n}
  f g h : Mor (n , Γ) σ

-- infixr 20 _`∘_

data Mor where
  `_ : ∀ {n x y} → Edge {n} x y → Mor (n , x) (` y)

  `id : Mor (suc zero , σ ∷ []) σ
  _`∘_  : Mor (suc zero , σ ∷ []) ρ → Mor (suc zero , τ ∷ []) σ → Mor (suc zero , τ ∷ []) ρ

  `idr   : f `∘ `id ≡ f
  `idl   : `id `∘ f ≡ f
  `assoc : f `∘ (g `∘ h) ≡ (f `∘ g) `∘ h
--
--   -- ⊗-elim
--   `match⊗ : ∀ {x y} → Mor Ψ (x `⊗ y) → Mor (Γ ++ x ∷ y ∷ Δ) τ → Mor (Γ ++ Ψ ++ Δ) τ
--   -- ⊗-intro
--   `⟨_,_⟩ : Mor Γ τ → Mor Δ σ → Mor (Γ ++ Δ) (τ `⊗ σ)
--
--   -- I-elim
--   `match₁ : Mor Ψ `I → Mor (Γ ++ Δ) τ → Mor (Γ ++ Ψ ++ Δ) τ
--   -- I-intro
--   `* : Mor [] `I
--
--   squash : is-set (Mor Γ σ)
--
-- module _ where
--   open Precategory
--
--   Free-mc : Precategory ℓ ℓ
--   Free-mc .Ob          = Ty
--   Free-mc .Hom         = Mor
--   Free-mc .Hom-set _ _ = squash
--   Free-mc .id          = `id
--   Free-mc ._∘_         = _`∘_
--   Free-mc .idr   _     = `idr
--   Free-mc .idl   _     = `idl
--   Free-mc .assoc _ _ _ = `assoc
--
--   open Monoidal-category
--
--   Free-monoidal : Monoidal-category Free-mc
--   Free-monoidal .-⊗- = record { F₀ = {! !} ; F₁ = {! !} ; F-id = {! !} ; F-∘ = {! !} }
--   Free-monoidal .Unit = {! !}
--   Free-monoidal .unitor-l = {! !}
--   Free-monoidal .unitor-r = {! !}
--   Free-monoidal .associator = {! !}
--   Free-monoidal .triangle = {! !}
--   Free-monoidal .pentagon = {! !}
