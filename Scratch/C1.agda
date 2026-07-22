module Scratch.C1 where

-- C1 (DEDUP): Strictification re-proves, at the specific universal arrow
-- ⊗-arr Γ, what Representable already proves for ANY universal arrow.
-- Every check below is `refl` (definitional interchangeability) except C1d,
-- which shows Rep.plug-nat directly INHABITS restrict-nat's type.

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import Multicategory.Unary
import Multicategory.Representable as Rep
import Multicategory.Strictification as St

module _ {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where
  open Premulticategory M
  open St M rep

  -- (C1a) restrict-equiv IS Rep.restrE at the universal arrow — definitionally.
  C1a : {Γ : List Obₘ} {z : Obₘ}
      → restrict-equiv {Γ} {z} ≡ Rep.restrE M (⊗-arr Γ) (⊗-arr-univ Γ)
  C1a = refl

  -- (C1b) restrict IS Rep.restr — definitionally.
  C1b : {Γ : List Obₘ} {z : Obₘ} (k : Homₘ (⊗₀ Γ ∷ []) z)
      → restrict k ≡ Rep.restr M (⊗-arr Γ) k
  C1b k = refl

  -- (C1c) Strictification.∘ₘ-substr IS Rep.∘ₘ-substr — definitionally
  -- (they are literally the same J-term).
  C1c : {B B' : List Obₘ} {w z : Obₘ}
        (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
      → ∘ₘ-substr a p m ≡ Rep.∘ₘ-substr M a p m
  C1c a p m = refl

  -- (C1d) Rep.plug-nat (⊗-arr Γ) directly inhabits restrict-nat's type:
  -- restrict-nat can be deleted and replaced by this one-liner.
  C1d : {Γ : List Obₘ} {w z : Obₘ}
        (a : Homₘ (w ∷ []) z) (φ : Homₘ (⊗₀ Γ ∷ []) w)
      → restrict {Γ} {z} (_∘ₘ_ {Θ = []} {Ξ = []} a φ)
        ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
            (_∘ₘ_ {Θ = []} {Ξ = []} a (restrict {Γ} {w} φ))
  C1d {Γ} = Rep.plug-nat M (⊗-arr Γ)

  -- (C1d') ... and it agrees with the existing proof pointwise (both are
  -- hom-set-valued so this is automatic, but check the statement matches).
  C1d-same-statement :
      {Γ : List Obₘ} {w z : Obₘ}
      (a : Homₘ (w ∷ []) z) (φ : Homₘ (⊗₀ Γ ∷ []) w)
    → restrict-nat a φ ≡ Rep.plug-nat M (⊗-arr Γ) a φ
  C1d-same-statement a φ = Homₘ-set _ _ _ _

  -- (C1e) expand IS Equiv.from of Rep.restrE — definitionally.
  C1e : {Γ : List Obₘ} {z : Obₘ} (m : Homₘ Γ z)
      → expand m ≡ Equiv.from (Rep.restrE M (⊗-arr Γ) (⊗-arr-univ Γ)) m
  C1e m = refl

  -- (C1f) The private ++-assoc-nil (Strictification, line 54) specialised at
  -- Ξ = [] is Rep.++-assoc-idr's statement.
  C1f : (Γ : List Obₘ)
      → ++-assoc Γ [] [] ≡ (λ i → [] ++ (++-idr Γ i) ++ [])
  C1f = Rep.++-assoc-idr M
