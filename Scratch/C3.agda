module Scratch.C3 where

-- C2 stretch test: rewrite splitμ (Strictification lines 937-1050, ~113 lines
-- of subst-∙/ap-∙ shuffling) with the PathP kit from Scratch.C2.
--
-- Structure of the new proof: each algebraic move is ONE named PathP
--   s1  pull ⊗-arr Ε into μ            (assocˢ' : cleaned assocₘ, Θ,Φ singletons)
--   s2  plug ⊗-arr Δ along s1          (∘ₘ-pathp, free)
--   s3  pull ⊗-arr Δ into μ            (assocˢ  : cleaned assocₘ, Φ = [])
--   s4  collapse μ-block to ⊗-arr(Δ++Ε) (ic₂ + restrict₂-μ)
--   s5  plug s4 into χ                 (∘ₘ-pathp, free)
--   t*  plug ⊗-arr Γ along everything  (∘ₘ-pathp, free)
--   ic₂ reorder the Γ/(Δ++Ε) plugs     (homogeneous!)
-- composed with _∙P_ and reconciled ONCE against the canonical list path
-- (spine-coh, whose content is the analogue of the old splitμ-inner).

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
import Multicategory.Representable as Rep
import Multicategory.Strictification as St

module _ {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where
  open Premulticategory M
  open St M rep using
    (⊗₀ ; ⊗-arr ; μ ; restrict₂-μ ; module restrict₂ ; module restrict₃)

  -- ================= kit (as in Scratch.C2) =================

  ∘ₘ-pathp : {Θ Θ' Ξ Ξ' Γ Γ' : List Obₘ} {x z : Obₘ}
             (P : Θ ≡ Θ') (Q : Ξ ≡ Ξ') (G : Γ ≡ Γ')
             {f : Homₘ (Θ ++ x ∷ Ξ) z} {f' : Homₘ (Θ' ++ x ∷ Ξ') z}
             {g : Homₘ Γ x} {g' : Homₘ Γ' x}
           → PathP (λ i → Homₘ (P i ++ x ∷ Q i) z) f f'
           → PathP (λ i → Homₘ (G i) x) g g'
           → PathP (λ i → Homₘ (P i ++ G i ++ Q i) z) (f ∘ₘ g) (f' ∘ₘ g')
  ∘ₘ-pathp P Q G ff gg i = _∘ₘ_ {Θ = P i} {Ξ = Q i} (ff i) (gg i)

  hom-over : {Γ Γ' : List Obₘ} {z : Obₘ} {p q : Γ ≡ Γ'} (α : p ≡ q)
             {f : Homₘ Γ z} {g : Homₘ Γ' z}
           → PathP (λ i → Homₘ (p i) z) f g → PathP (λ i → Homₘ (q i) z) f g
  hom-over {z = z} α {f} {g} = subst (λ r → PathP (λ i → Homₘ (r i) z) f g) α

  private
    ++-assoc-nil : (Γ Ξ : List Obₘ) → ++-assoc Γ [] Ξ ≡ ap (_++ Ξ) (++-idr Γ)
    ++-assoc-nil []      Ξ = refl
    ++-assoc-nil (a ∷ Γ) Ξ = ap (ap (a ∷_)) (++-assoc-nil Γ Ξ)

    flatten-nil-mid : (Γ Ε : List Obₘ)
                    → interchange-flatten Γ [] Ε [] ≡ ap (_++ (Ε ++ [])) (++-idr Γ)
    flatten-nil-mid []      Ε = refl
    flatten-nil-mid (a ∷ Γ) Ε = ap (ap (a ∷_)) (flatten-nil-mid Γ Ε)

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

  -- assocₘ with singleton prefix Θ = w ∷ [], Φ = []: junk absorbed.
  assocˢ : {Ξ Ψ Ρ : List Obₘ} {w x y z : Obₘ}
           (f : Homₘ (w ∷ x ∷ Ξ) z) (g : Homₘ (y ∷ Ψ) x) (h : Homₘ Ρ y)
         → PathP (λ i → Homₘ (assocₘ-boundary (w ∷ []) [] Ρ Ψ Ξ i) z)
             (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f g) h)
             (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f (_∘ₘ_ {Θ = []} {Ξ = Ψ} g h))
  assocˢ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = w' ∷ []} {Ξ = Ψ ++ Ξ} q h) (sym (transport-refl (f ∘ₘ g)))
      ◁ assocₘ {Θ = w' ∷ []} {Ξ = Ξ} {Φ = []} f g h
    where w' = _
  -- assocₘ with singleton prefixes Θ = w ∷ [], Φ = v ∷ [], Ξ = Ψ = []: junk absorbed.
  assocˢ' : {Ρ : List Obₘ} {w v x y z : Obₘ}
            (f : Homₘ (w ∷ x ∷ []) z) (g : Homₘ (v ∷ y ∷ []) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary (w ∷ []) (v ∷ []) Ρ [] [] i) z)
              (_∘ₘ_ {Θ = w ∷ v ∷ []} {Ξ = []} (_∘ₘ_ {Θ = w ∷ []} {Ξ = []} f g) h)
              (_∘ₘ_ {Θ = w ∷ []} {Ξ = []} f (_∘ₘ_ {Θ = v ∷ []} {Ξ = []} g h))
  assocˢ' f g h =
    ap (λ q → _∘ₘ_ {Θ = _ ∷ _ ∷ []} {Ξ = []} q h) (sym (transport-refl (f ∘ₘ g)))
      ◁ assocₘ {Θ = _ ∷ []} {Ξ = []} {Φ = _ ∷ []} f g h

  -- ================= splitμ, re-proven =================

  private
    -- The one spine reconciliation (replaces splitμ-inner + all per-site
    -- subst-∙/ap-∙ shuffling).
    inner-coh : (Δ Ε : List Obₘ)
      → ((ap (Δ ++_) (sym (++-assoc Ε [] [])) ∙ sym (++-assoc Δ (Ε ++ []) []))
          ∙ ap (_++ []) (ap (Δ ++_) (++-idr Ε))) ∙ ++-idr (Δ ++ Ε)
        ≡ ap (Δ ++_) (++-idr Ε)
    inner-coh [] Ε =
        ap (λ t → (t ∙ ap (_++ []) (++-idr Ε)) ∙ ++-idr Ε)
           (∙-idr (sym (++-assoc Ε [] [])) ∙ ap sym (++-assoc-nil Ε []))
      ∙ ap (_∙ ++-idr Ε) (∙-invl (ap (_++ []) (++-idr Ε)))
      ∙ ∙-idl (++-idr Ε)
    inner-coh (a ∷ Δ) Ε =
        ap (λ t → (t ∙ ap (_++ []) (ap ((a ∷ Δ) ++_) (++-idr Ε))) ∙ ++-idr ((a ∷ Δ) ++ Ε))
           (sym (ap-∙ (a ∷_) l₁ l₂))
      ∙ ap (_∙ ++-idr ((a ∷ Δ) ++ Ε)) (sym (ap-∙ (a ∷_) (l₁ ∙ l₂) l₃))
      ∙ sym (ap-∙ (a ∷_) ((l₁ ∙ l₂) ∙ l₃) (++-idr (Δ ++ Ε)))
      ∙ ap (ap (a ∷_)) (inner-coh Δ Ε)
      where
        l₁ = ap (Δ ++_) (sym (++-assoc Ε [] []))
        l₂ = sym (++-assoc Δ (Ε ++ []) [])
        l₃ = ap (_++ []) (ap (Δ ++_) (++-idr Ε))

  splitμ' : {Γ Δ Ε : List Obₘ} {z : Obₘ} (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ (Δ ++ Ε) ∷ []) z)
          → restrict₂.to {Γ} {Δ ++ Ε} χ
            ≡ restrict₃.to {Γ} {Δ} {Ε} (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ (μ Δ Ε))
  splitμ' {Γ} {Δ} {Ε} {z} χ = sym (from-pathp (hom-over spine-coh chain))
    where
      BΩ : List Obₘ → Type _
      BΩ Ω = Homₘ Ω z
      μᵍ    = μ Δ Ε
      arrDE = ⊗-arr (Δ ++ Ε)
      W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z
      W = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μᵍ
      μEE : Homₘ (⊗₀ Δ ∷ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μEE = _∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} μᵍ (⊗-arr Ε)
      μbb : Homₘ (Δ ++ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μbb = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} μEE (⊗-arr Δ)
      -- canonical list paths
      P-DE = ap (Δ ++_) (++-idr Ε)
      q̄    = sym (++-assoc Ε [] [])
      r̄    = sym (++-assoc Δ (Ε ++ []) [])
      i2 = ap (Δ ++_) q̄
      i5 = ap (_++ []) P-DE
      p2 = ap (Γ ++_) i2
      p3 = ap (Γ ++_) r̄
      p5 = ap (Γ ++_) i5
      P₂ap = ap (Γ ++_) (++-idr (Δ ++ Ε))
      P₃   = ap (Γ ++_) P-DE
      -- s1: pull ⊗-arr Ε into μ.
      s1 : PathP (λ i → Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ q̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE)
      s1 = assocˢ' χ μᵍ (⊗-arr Ε)
      -- s2: plug ⊗-arr Δ along s1.
      s2 : PathP (λ i → Homₘ (⊗₀ Γ ∷ Δ ++ q̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE) (⊗-arr Δ))
      s2 = ∘ₘ-pathp refl q̄ refl s1 refl
      -- s3: pull ⊗-arr Δ into μEE.
      s3 : PathP (λ i → Homₘ (⊗₀ Γ ∷ r̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE) (⊗-arr Δ))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μbb)
      s3 = assocˢ χ μEE (⊗-arr Δ)
      -- s4: the μ-block collapse, as a clean PathP.
      s4 : PathP (λ i → Homₘ (P-DE i) (⊗₀ (Δ ++ Ε))) μbb arrDE
      s4 = sym (ic₂ μᵍ (⊗-arr Δ) (⊗-arr Ε))
             ◁ to-pathp {A = λ i → Homₘ (P-DE i) (⊗₀ (Δ ++ Ε))} (restrict₂-μ Δ Ε)
      -- s5: plug s4 into χ.
      s5 : PathP (λ i → Homₘ (⊗₀ Γ ∷ P-DE i ++ []) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μbb)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ arrDE)
      s5 = ∘ₘ-pathp refl refl P-DE refl s4
      -- t*: plug ⊗-arr Γ along s2, s3, s5.
      t2 : PathP (λ i → Homₘ (p2 i) z) _ _
      t2 = ∘ₘ-pathp refl i2 refl s2 (λ _ → ⊗-arr Γ)
      t3 : PathP (λ i → Homₘ (p3 i) z) _ _
      t3 = ∘ₘ-pathp refl r̄ refl s3 (λ _ → ⊗-arr Γ)
      t5 : PathP (λ i → Homₘ (p5 i) z) _ _
      t5 = ∘ₘ-pathp refl i5 refl s5 (λ _ → ⊗-arr Γ)
      canon : Homₘ (Γ ++ ((Δ ++ Ε) ++ [])) z
      canon = _∘ₘ_ {Θ = Γ} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ (Δ ++ Ε) ∷ []} χ (⊗-arr Γ)) arrDE
      -- assemble; reorder the Γ/(Δ++Ε) plugs; land on restrict₂.to χ.
      chain : PathP (λ i → Homₘ ((((p2 ∙ p3) ∙ p5) ∙ P₂ap) i) z)
                (_∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
                  (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
                  (⊗-arr Γ))
                (restrict₂.to {Γ} {Δ ++ Ε} χ)
      chain =
        _∙P_ {B = BΩ} {p = (p2 ∙ p3) ∙ p5} {q = P₂ap}
          ( (_∙P_ {B = BΩ} {p = p2 ∙ p3} {q = p5}
              (_∙P_ {B = BΩ} {p = p2} {q = p3} t2 t3)
              t5)
            ▷ sym (ic₂ χ (⊗-arr Γ) arrDE) )
          (transport-filler (λ i → BΩ (P₂ap i)) canon)
      -- the single spine reconciliation
      spine-coh : ((p2 ∙ p3) ∙ p5) ∙ P₂ap ≡ P₃
      spine-coh =
          ap (λ t → (t ∙ p5) ∙ P₂ap) (sym (ap-∙ (Γ ++_) i2 r̄))
        ∙ ap (_∙ P₂ap) (sym (ap-∙ (Γ ++_) (i2 ∙ r̄) i5))
        ∙ sym (ap-∙ (Γ ++_) ((i2 ∙ r̄) ∙ i5) (++-idr (Δ ++ Ε)))
        ∙ ap (ap (Γ ++_)) (inner-coh Δ Ε)
