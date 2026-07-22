module Scratch.C2 where

-- C2 (PathP kit): stay in PathP land instead of converting every law to
-- subst form and shuffling subst-∙/ap-∙.
--
-- The kit:
--   * ∘ₘ-pathp  — the heterogeneous congruence for ∘ₘ, FREE because _∘ₘ_ is
--                 polymorphic in Θ/Ξ/Γ.
--   * hom-over  — reconcile the base path of a PathP of homs (one subst).
--   * ic₂       — interchangeₘ for binary maps χ : Homₘ (x ∷ y ∷ []) z,
--                 with all transport-refl junk and the slot₁-subst absorbed
--                 ONCE.  Crucially its statement is HOMOGENEOUS (both plug
--                 orders land in Homₘ (Γ ++ Δ ++ []) z definitionally).
--   * assocᵘ    — assocₘ with unary outer map (Θ = Ξ = Φ = []), the
--                 slot-unbury transport-refl absorbed; stated as a PathP over
--                 sym (++-assoc Ρ Ψ []).
--
-- Payoff measured below: μ-block 45 → 4 lines, μ-unit-r's swap-eq 33 → 5,
-- μg-collapse 47 → 3, eqΓ 10 → 1.

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
import Multicategory.Representable as Rep
import Multicategory.Strictification as St

module _ {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where
  open Premulticategory M
  open St M rep using (⊗₀ ; ⊗-arr ; μ ; restrict₂-μ ; μ-unit-r ; ≅to)

  -- ======================= the kit =======================

  -- (K1) Heterogeneous congruence for ∘ₘ: free.
  ∘ₘ-pathp : {Θ Θ' Ξ Ξ' Γ Γ' : List Obₘ} {x z : Obₘ}
             (P : Θ ≡ Θ') (Q : Ξ ≡ Ξ') (G : Γ ≡ Γ')
             {f : Homₘ (Θ ++ x ∷ Ξ) z} {f' : Homₘ (Θ' ++ x ∷ Ξ') z}
             {g : Homₘ Γ x} {g' : Homₘ Γ' x}
           → PathP (λ i → Homₘ (P i ++ x ∷ Q i) z) f f'
           → PathP (λ i → Homₘ (G i) x) g g'
           → PathP (λ i → Homₘ (P i ++ G i ++ Q i) z) (f ∘ₘ g) (f' ∘ₘ g')
  ∘ₘ-pathp P Q G ff gg i = _∘ₘ_ {Θ = P i} {Ξ = Q i} (ff i) (gg i)

  -- (K2) Reconcile the base path of a PathP of homs.
  hom-over : {Γ Γ' : List Obₘ} {z : Obₘ} {p q : Γ ≡ Γ'} (α : p ≡ q)
             {f : Homₘ Γ z} {g : Homₘ Γ' z}
           → PathP (λ i → Homₘ (p i) z) f g → PathP (λ i → Homₘ (q i) z) f g
  hom-over {z = z} α {f} {g} = subst (λ r → PathP (λ i → Homₘ (r i) z) f g) α

  -- Spine lemmas (private in Strictification; re-proven here only because the
  -- scratch module cannot see them — in situ the kit reuses the existing ones).
  private
    ++-assoc-nil : (Γ Ξ : List Obₘ) → ++-assoc Γ [] Ξ ≡ ap (_++ Ξ) (++-idr Γ)
    ++-assoc-nil []      Ξ = refl
    ++-assoc-nil (a ∷ Γ) Ξ = ap (ap (a ∷_)) (++-assoc-nil Γ Ξ)

    flatten-nil-mid : (Γ Ε : List Obₘ)
                    → interchange-flatten Γ [] Ε [] ≡ ap (_++ (Ε ++ [])) (++-idr Γ)
    flatten-nil-mid []      Ε = refl
    flatten-nil-mid (a ∷ Γ) Ε = ap (ap (a ∷_)) (flatten-nil-mid Γ Ε)

  -- (K3) Binary interchange, cleaned: for χ : Homₘ (x ∷ y ∷ []) z the two
  -- plug orders agree HOMOGENEOUSLY in Homₘ (Γ ++ Δ ++ []) z.
  ic₂ : {x y z : Obₘ} {Γ Δ : List Obₘ}
        (χ : Homₘ (x ∷ y ∷ []) z) (g : Homₘ Γ x) (h : Homₘ Δ y)
      → _∘ₘ_ {Θ = Γ} {Ξ = []} (_∘ₘ_ {Θ = []} {Ξ = y ∷ []} χ g) h
        ≡ _∘ₘ_ {Θ = []} {Ξ = Δ ++ []} (_∘ₘ_ {Θ = x ∷ []} {Ξ = []} χ h) g
  ic₂ {x} {y} {z} {Γ} {Δ} χ g h =
      hom-over loop-refl
        (_∙P_ {B = λ Ω → Homₘ Ω z}
           {p = ap (_++ Δ ++ []) (sym (++-idr Γ))}
           {q = interchange-flatten Γ [] Δ []}
           leg
           (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Γ} {Δ = Δ} χ g h))
    ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Δ ++ []} q g)
         ( transport-refl _
         ∙ ap (λ q → _∘ₘ_ {Θ = x ∷ []} {Ξ = []} q h) (transport-refl χ) )
    where
      BΩ : List Obₘ → Type _
      BΩ Ω = Homₘ Ω z
      S₁ : Γ ++ y ∷ [] ≡ (Γ ++ []) ++ y ∷ []
      S₁ = interchange-slot₁ [] Γ [] y []
      χg : Homₘ (Γ ++ y ∷ []) z
      χg = _∘ₘ_ {Θ = []} {Ξ = y ∷ []} χ g
      slotP : PathP (λ i → Homₘ (sym (++-idr Γ) i ++ y ∷ []) z)
                χg (subst BΩ S₁ χg)
      slotP = subst (λ r → PathP (λ i → Homₘ (r i) z) χg (subst BΩ S₁ χg))
                (ap sym (++-assoc-nil Γ (y ∷ [])))
                (transport-filler (λ i → BΩ (S₁ i)) χg)
      leg : PathP (λ i → Homₘ (sym (++-idr Γ) i ++ Δ ++ []) z)
              (_∘ₘ_ {Θ = Γ} {Ξ = []} χg h)
              (_∘ₘ_ {Θ = Γ ++ []} {Ξ = []} (subst BΩ S₁ χg) h)
      leg = ∘ₘ-pathp (sym (++-idr Γ)) refl refl slotP refl
      loop-refl : (ap (_++ Δ ++ []) (sym (++-idr Γ)) ∙ interchange-flatten Γ [] Δ [])
                ≡ refl
      loop-refl =
          ap (ap (_++ Δ ++ []) (sym (++-idr Γ)) ∙_) (flatten-nil-mid Γ Δ)
        ∙ sym (ap-∙ (_++ Δ ++ []) (sym (++-idr Γ)) (++-idr Γ))
        ∙ ap (ap (_++ Δ ++ [])) (∙-invl (++-idr Γ))

  -- (K4) assocₘ with unary outer map, junk absorbed, as a clean PathP.
  assocᵘ : {Ψ Ρ : List Obₘ} {x y z : Obₘ}
           (f : Homₘ (x ∷ []) z) (g : Homₘ (y ∷ Ψ) x) (h : Homₘ Ρ y)
         → PathP (λ i → Homₘ (assocₘ-boundary [] [] Ρ Ψ [] i) z)
             (_∘ₘ_ {Θ = []} {Ξ = Ψ ++ []} (_∘ₘ_ {Θ = []} {Ξ = []} f g) h)
             (_∘ₘ_ {Θ = []} {Ξ = []} f (_∘ₘ_ {Θ = []} {Ξ = Ψ} g h))
  assocᵘ {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Ψ ++ []} q h) (sym (transport-refl (f ∘ₘ g)))
      ◁ assocₘ {Θ = []} {Ξ = []} {Φ = []} f g h

  -- ================== the rewrites (measure) ==================

  -- μ-block: 45 lines (Strictification 851-895) → 4 lines.
  μ-block' : (Δ Ε : List Obₘ)
           → _∘ₘ_ {Θ = []} {Ξ = Ε ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)) (⊗-arr Δ)
             ≡ subst (λ Ω → Homₘ Ω (⊗₀ (Δ ++ Ε))) (sym (ap (Δ ++_) (++-idr Ε)))
                 (⊗-arr (Δ ++ Ε))
  μ-block' Δ Ε =
      sym (ic₂ (μ Δ Ε) (⊗-arr Δ) (⊗-arr Ε))
    ∙ from-pathp⁻ (to-pathp {A = λ i → Homₘ (ap (Δ ++_) (++-idr Ε) i) (⊗₀ (Δ ++ Ε))}
        (restrict₂-μ Δ Ε))

  -- μ-unit-r's swap-eq: 33 lines (Strictification 615-651) → 5 lines.
  swap-eq' : (Y : List Obₘ)
           → _∘ₘ_ {Θ = []} {Ξ = []}
               (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])) (⊗-arr Y)
             ≡ ⊗-arr (Y ++ [])
  swap-eq' Y =
      sym (ic₂ (μ Y []) (⊗-arr Y) (⊗-arr []))
    ∙ sym (transport-refl _)
    ∙ restrict₂-μ Y []

  -- μg-collapse: 47 lines (Strictification 687-733) → 3 lines.
  μg-collapse' : (Y Δ : List Obₘ) (g' : Homₘ Δ (⊗₀ Y))
               → _∘ₘ_ {Θ = Δ} {Ξ = []}
                   (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) g') (⊗-arr [])
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr Y)))) g'
  μg-collapse' Y Δ g' =
      ic₂ (μ Y []) g' (⊗-arr [])
    ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q g') (μ-unit-r Y)

  -- The four subst-pushing J-lemmas (∘ₘ-substr/∘ₘ-substl/∘ₘ-substrG/
  -- ∘ₘ-subst-suf, ~40 lines total) are each a 2-line corollary of
  -- ∘ₘ-pathp + transport-filler.  Two representatives:
  ∘ₘ-substrG' : {Θ Ξ B B' : List Obₘ} {w z : Obₘ}
                (a : Homₘ (Θ ++ w ∷ Ξ) z) (p : B ≡ B') (m : Homₘ B w)
              → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} a (subst (λ Ω → Homₘ Ω w) p m)
                ≡ subst (λ Ω → Homₘ (Θ ++ Ω ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} a m)
  ∘ₘ-substrG' {Θ} {Ξ} {w = w} a p m = sym (from-pathp
    (∘ₘ-pathp refl refl p refl (transport-filler (λ i → Homₘ (p i) w) m)))

  ∘ₘ-substl' : {Θ Θ' Ξ Γ : List Obₘ} {x z : Obₘ}
               (p : Θ ≡ Θ') (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
             → _∘ₘ_ {Θ = Θ'} {Ξ = Ξ} (subst (λ Ω → Homₘ (Ω ++ x ∷ Ξ) z) p f) g
               ≡ subst (λ Ω → Homₘ (Ω ++ Γ ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-substl' {Θ} {Θ'} {Ξ} {x = x} {z} p f g = sym (from-pathp
    (∘ₘ-pathp p refl refl
      (transport-filler (λ i → Homₘ (p i ++ x ∷ Ξ) z) f) refl))

  -- eqΓ: 10 lines (Strictification 309-318) → 1 line.
  eqΓ' : {Γ Δ : List Obₘ} {w z : Obₘ}
         (a : Homₘ (w ∷ []) z) (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) w)
       → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} a χ) (⊗-arr Γ)
         ≡ subst (λ Ω → Homₘ Ω z) (++-assoc Γ (⊗₀ Δ ∷ []) [])
             (_∘ₘ_ {Θ = []} {Ξ = []} a (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} χ (⊗-arr Γ)))
  eqΓ' {Γ} {Δ} a χ = from-pathp⁻ (assocᵘ a χ (⊗-arr Γ))
