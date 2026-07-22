module Scratch.A5 where

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr)

open import Multicategory
import Multicategory.Representable as Rep
import Multicategory.Strictification as Str

-- A5/dedup: Strictification re-proves, verbatim or as a special case,
-- machinery already exported by Representable (which it imports).

module _ {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where
  open Premulticategory M
  private module S = Str M rep

  -- 1. Strictification.restrict is DEFINITIONALLY Rep.restr at the universal
  --    arrow (the comment in Representable line 61 claims this; confirmed).
  _ : {Γ : List Obₘ} {z : Obₘ} → S.restrict {Γ} {z} ≡ Rep.restr M (S.⊗-arr Γ) {z}
  _ = refl

  -- 2. Hence Strictification.restrict-nat (32 lines incl. its private
  --    path-eq lemma usage) is exactly Rep.plug-nat at u = ⊗-arr Γ:
  restrict-nat' : {Γ : List Obₘ} {w z : Obₘ}
                  (a : Homₘ (w ∷ []) z) (φ : Homₘ (S.⊗₀ Γ ∷ []) w)
                → S.restrict {Γ} {z} (_∘ₘ_ {Θ = []} {Ξ = []} a φ)
                  ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
                      (_∘ₘ_ {Θ = []} {Ξ = []} a (S.restrict {Γ} {w} φ))
  restrict-nat' {Γ} = Rep.plug-nat M (S.⊗-arr Γ)

  -- 3. Strictification.∘ₘ-substr is verbatim Representable.∘ₘ-substr:
  ∘ₘ-substr' : {B B' : List Obₘ} {w z : Obₘ}
               (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
             → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) p m)
               ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) p (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  ∘ₘ-substr' = Rep.∘ₘ-substr M
