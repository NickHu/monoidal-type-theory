open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties
open import Data.Set.Coequaliser using (_/_ ; inc ; quot ; squash ; Coeq-elim-prop)

open import Multicategory
open import Multicategory.Free
open import Multicategory.Functor using (Multifunctor ; map-++₂)
import Multicategory.Representable as Rep
import Multicategory.Free.Eval as EvalMod

-- Uniqueness half of the freeness theorem (Shulman, Theorem 2.4.10): any
-- multifunctor FMonCat G → M that agrees with the generators and strictly
-- preserves the chosen representability data (⦅var,var⦆ ↦ a universal arrow,
-- ⋆ ↦ a universal arrow) is the evaluation multifunctor.
--
-- Strategy: the heart is a SYMMETRIC statement (module Core below): two
-- "strict extensions" — multifunctor field triples whose object part is
-- ⟦_⟧ᵗ on the nose — that agree on generators, ⦅var,var⦆ and ⋆ (the latter
-- two with a universality witness) agree on every morphism.  Because both
-- sides run through the SAME syntactic decompositions, all base-path
-- bookkeeping cancels: each case is homogeneous equational reasoning via
-- castₘ-inj and from-pathp'd composition laws.  The packaged theorem
-- (arbitrary F₀ with pointwise agreement paths) then follows by transporting
-- the given multifunctor onto ⟦_⟧ᵗ.

module Multicategory.Free.Uniqueness
  {o h o' h'} (G : Multigraph o h)
  (M : Premulticategory o' h') (rep : Rep.is-representable M)
  (φ : EvalMod.Multigraph-hom↓ G M rep)
  where

open import Multicategory.Free.SplitLemmas G
open import Multicategory.Free.Multicategory G
  using (Homᶠ ; idᶠ ; _∘ᶠ_ ; incᵖ ; incᵖᵖ ; FMonCat)
open import Multicategory.Free.Representable G
  using (sec⊗ ; sec𝟙 ; split-here~ʳ)
open import Multicategory.Free.Freeness G M rep φ
  using (⟦_⟧ᵗ ; ⟦_⟧ᶜ ; ⟦⟧-++ ; ⟦⟧-++₂ ; eval ; evalᶠ ; Eval-multifunctor)

private
  module G = Multigraph G
  module M = Premulticategory M
  module E = EvalMod G M rep

open E using (⊗M ; uM ; uM-universal ; castₘ)

private variable
  x y z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Κ Γ₁ Δ₁ : Ctx
  As : List G.Ob

-- ==========================================================================
-- Kit: PathP composition over composite bases (generic), paths-over at the
-- Homᶠ level packaged with their base (so decompositions never have to
-- commit to a canonical base path), and injectivity of castₘ.
-- ==========================================================================

∙P-over : ∀ {ℓ ℓ'} {X : Type ℓ} (P : X → Type ℓ') {a b c : X}
          {p : a ≡ b} {q : b ≡ c} {u : P a} {v : P b} {w : P c}
        → PathP (λ i → P (p i)) u v → PathP (λ i → P (q i)) v w
        → PathP (λ i → P ((p ∙ q) i)) u w
∙P-over P {p = p} {q = q} {u = u} {v = v} {w = w} α β i =
  comp (λ j → P (∙-filler p q j i)) (∂ i) λ where
    j (j = i0) → α i
    j (i = i0) → u
    j (i = i1) → β j

-- A morphism path over an unspecified base: the base is DATA, so segments
-- built from fillers and interval-congruences compose without ever
-- reconciling base paths.
Overᶠ : (Γ Δ : Ctx) (z : Ty) → Homᶠ Γ z → Homᶠ Δ z → Type (o ⊔ h)
Overᶠ Γ Δ z f g = Σ[ b ∈ Γ ≡ Δ ] PathP (λ i → Homᶠ (b i) z) f g

infixr 30 _∙O_
_∙O_ : {f : Homᶠ Γ z} {g : Homᶠ Δ z} {k : Homᶠ Κ z}
     → Overᶠ Γ Δ z f g → Overᶠ Δ Κ z g k → Overᶠ Γ Κ z f k
_∙O_ {z = z} (b , α) (c , β) = b ∙ c , ∙P-over (λ Ω → Homᶠ Ω z) α β

-- The same at the spine level (used by the generator decomposition).
OverSp : (Γ Δ : Ctx) (As : List G.Ob) → Sp Γ As → Sp Δ As → Type (o ⊔ h)
OverSp Γ Δ As ts us = Σ[ b ∈ Γ ≡ Δ ] PathP (λ i → Sp (b i) As) ts us

infixr 30 _∙S_
_∙S_ : {ts : Sp Γ As} {us : Sp Δ As} {vs : Sp Κ As}
     → OverSp Γ Δ As ts us → OverSp Δ Κ As us vs → OverSp Γ Κ As ts vs
_∙S_ {As = As} (b , α) (c , β) = b ∙ c , ∙P-over (λ Ω → Sp Ω As) α β

-- Transport in the hom-sets of M is injective.
castₘ-inj : {Ω₀ Ω₁ : List M.Obₘ} {w : M.Obₘ} (p : Ω₀ ≡ Ω₁)
            {f g : M.Homₘ Ω₀ w} → castₘ p f ≡ castₘ p g → f ≡ g
castₘ-inj {w = w} p {f} {g} q =
    sym (transport⁻transport (λ i → M.Homₘ (p i) w) f)
  ∙ ap (castₘ (sym p)) q
  ∙ transport⁻transport (λ i → M.Homₘ (p i) w) g

-- ==========================================================================
-- Strict extensions: the fields of a multifunctor FMonCat G → M whose
-- object part is ⟦_⟧ᵗ definitionally (note ⟦⟧-++₂ = map-++₂ ⟦_⟧ᵗ and
-- ⟦⟧-++ = map-++ ⟦_⟧ᵗ, so this is literally the Multifunctor interface
-- specialised at F₀ = ⟦_⟧ᵗ).
-- ==========================================================================

record Extension : Type (o ⊔ h ⊔ o' ⊔ h') where
  no-eta-equality
  field
    F₁  : ∀ {Γ z} → Homᶠ Γ z → M.Homₘ ⟦ Γ ⟧ᶜ ⟦ z ⟧ᵗ
    F-id : ∀ {z} → F₁ (idᶠ {z}) ≡ M.idₘ
    F-∘ : ∀ {Θ Ξ Γ x z} (f : Homᶠ (Θ ++ x ∷ Ξ) z) (g : Homᶠ Γ x)
        → PathP (λ i → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ i) ⟦ z ⟧ᵗ)
            (F₁ (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g))
            (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
              (castₘ (⟦⟧-++ Θ (x ∷ Ξ)) (F₁ f)) (F₁ g))

-- The evaluation multifunctor is a strict extension.
Eval-ext : Extension
Eval-ext .Extension.F₁ = evalᶠ
Eval-ext .Extension.F-id = refl
Eval-ext .Extension.F-∘ = Eval-multifunctor .Multifunctor.F-∘ₘ

module _ (X : Extension) where
  private module X = Extension X

  -- The composition law, homogeneously (transport the left-hand side).
  ∘-hom : ∀ {Θ Ξ Γ x z} (f : Homᶠ (Θ ++ x ∷ Ξ) z) (g : Homᶠ Γ x)
        → castₘ (⟦⟧-++₂ Θ Γ Ξ) (X.F₁ (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g))
        ≡ M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
            (castₘ (⟦⟧-++ Θ (x ∷ Ξ)) (X.F₁ f)) (X.F₁ g)
  ∘-hom f g = from-pathp (X.F-∘ f g)

  -- F₁ applied under the interval to a path-over, homogenised.
  F₁-over : {b : Γ ≡ Δ} {f : Homᶠ Γ z} {g : Homᶠ Δ z}
          → PathP (λ i → Homᶠ (b i) z) f g
          → castₘ (ap ⟦_⟧ᶜ b) (X.F₁ f) ≡ X.F₁ g
  F₁-over D = from-pathp (λ i → X.F₁ (D i))

-- ==========================================================================
-- Syntactic decomposition lemmas.  Each expresses a term constructor as a
-- ∘ᶠ-composite of simpler classes, as an Overᶠ (path over an unspecified
-- structural base).  Both extensions are pushed through the SAME
-- decomposition, so the bases never need reconciling downstream.
-- ==========================================================================

-- ++-assoc against the empty middle is whiskered ++-idr (cons-by-cons).
assoc-idr : ∀ (Γ Δ : Ctx) → ++-assoc Γ [] Δ ≡ ap (_++ Δ) (++-idr Γ)
assoc-idr []      Δ = refl
assoc-idr (a ∷ Γ) Δ = ap (ap (a ∷_)) (assoc-idr Γ Δ)

-- ⦅P,Q⦆ is the composite of the binary pairing of variables with P and Q.
decomp-⊗ : (P : Tm Γ₁ A) (Q : Tm Δ₁ B)
         → Overᶠ (Γ₁ ++ Δ₁ ++ []) (Γ₁ ++ Δ₁) (A ⊗ B)
             (_∘ᶠ_ {Θ = Γ₁} {Ξ = []}
               (_∘ᶠ_ {Θ = []} {Ξ = B ∷ []}
                 (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)) (inc P))
               (inc Q))
             (inc ⦅ P , Q ⦆)
decomp-⊗ {Γ₁ = Γ₁} {A = A} {Δ₁ = Δ₁} {B = B} P Q =
  seg1 ∙O seg2a ∙O seg2b ∙O seg3 ∙O seg4
  where
    P† : Tm (Γ₁ ++ []) A
    P† = cast (sym (++-idr Γ₁)) P

    Q† : Tm (Δ₁ ++ []) B
    Q† = cast (sym (++-idr Δ₁)) Q

    X : Tm ((Γ₁ ++ []) ++ B ∷ []) (A ⊗ B)
    X = ⦅_,_⦆ {Γ = Γ₁ ++ []} {Δ = B ∷ []} P† var

    c₁ : (Γ₁ ++ []) ++ B ∷ [] ≡ Γ₁ ++ B ∷ []
    c₁ = flattenˡ [] Γ₁ [] (B ∷ []) ∙ refl

    α₁ : sym c₁ ≡ (λ i → ++-idr Γ₁ (~ i) ++ B ∷ [])
    α₁ = ap sym (∙-idr (flattenˡ [] Γ₁ [] (B ∷ [])) ∙ assoc-idr Γ₁ (B ∷ []))

    W : PathP (λ i → Tm (++-idr Γ₁ (~ i) ++ B ∷ []) (A ⊗ B)) (cast c₁ X) X
    W = tm-over α₁ (symP (cast-filler c₁ X))

    seg1 : Overᶠ (Γ₁ ++ Δ₁ ++ []) ((Γ₁ ++ []) ++ Δ₁ ++ []) (A ⊗ B)
             (_∘ᶠ_ {Θ = Γ₁} {Ξ = []}
               (_∘ᶠ_ {Θ = []} {Ξ = B ∷ []}
                 (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)) (inc P))
               (inc Q))
             (inc (sub (split-here (Γ₁ ++ []) B []) X Q))
    seg1 = (λ i → ++-idr Γ₁ (~ i) ++ Δ₁ ++ [])
         , λ i → inc (sub (split-here (++-idr Γ₁ (~ i)) B []) (W i) Q)

    seg2a : Overᶠ ((Γ₁ ++ []) ++ Δ₁ ++ []) (((Γ₁ ++ []) ++ []) ++ Δ₁ ++ [])
              (A ⊗ B)
              (inc (sub (split-here (Γ₁ ++ []) B []) X Q))
              (inc (sub (split-++ʳ (Γ₁ ++ []) here) X Q))
    seg2a = (λ i → ++-idr (Γ₁ ++ []) (~ i) ++ Δ₁ ++ [])
          , λ i → inc (sub (split-here~ʳ (Γ₁ ++ []) B [] i) X Q)

    c₂ : (Γ₁ ++ []) ++ Δ₁ ++ [] ≡ ((Γ₁ ++ []) ++ []) ++ Δ₁ ++ []
    c₂ = flattenʳ (Γ₁ ++ []) [] Δ₁ [] ∙ refl

    seg2b : Overᶠ (((Γ₁ ++ []) ++ []) ++ Δ₁ ++ []) (((Γ₁ ++ []) ++ []) ++ Δ₁ ++ [])
              (A ⊗ B)
              (inc (sub (split-++ʳ (Γ₁ ++ []) here) X Q))
              (inc (cast c₂ ⦅ P† , Q† ⦆))
    seg2b = refl
          , incᵖ (ap (λ (v : Split-++ (Γ₁ ++ []) (B ∷ []) (split-++ʳ (Γ₁ ++ []) here))
                        → sub-pair v P† var Q)
                     (split-++-ʳ (Γ₁ ++ []) here))

    seg3 : Overᶠ (((Γ₁ ++ []) ++ []) ++ Δ₁ ++ []) ((Γ₁ ++ []) ++ Δ₁ ++ [])
              (A ⊗ B)
              (inc (cast c₂ ⦅ P† , Q† ⦆))
              (inc ⦅ P† , Q† ⦆)
    seg3 = sym c₂ , incᵖᵖ (symP (cast-filler c₂ ⦅ P† , Q† ⦆))

    seg4 : Overᶠ ((Γ₁ ++ []) ++ Δ₁ ++ []) (Γ₁ ++ Δ₁) (A ⊗ B)
              (inc ⦅ P† , Q† ⦆)
              (inc ⦅ P , Q ⦆)
    seg4 = (λ i → ++-idr Γ₁ i ++ ++-idr Δ₁ i)
         , λ i → inc ⦅ symP (cast-filler (sym (++-idr Γ₁)) P) i
                     , symP (cast-filler (sym (++-idr Δ₁)) Q) i ⦆

-- match⊗ P Q is the composite of match⊗ var Q with P (substituting P for
-- the matched variable).
decomp-m⊗ : ∀ {Γm Δm : Ctx} (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
          → Overᶠ (Γm ++ Ψ ++ Δm) (Γm ++ Ψ ++ Δm) C
              (_∘ᶠ_ {Θ = Γm} {Ξ = Δm}
                (inc (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Γm} {Δ = Δm} var Q))
                (inc P))
              (inc (match⊗ {Γ = Γm} {Δ = Δm} P Q))
decomp-m⊗ {Ψ = Ψ} {A = A} {B = B} {C = C} {Γm = Γm} {Δm = Δm} P Q =
  seg1 ∙O seg2 ∙O seg3 ∙O seg4
  where
    M⊗ : Tm (Γm ++ (A ⊗ B) ∷ Δm) C
    M⊗ = match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Γm} {Δ = Δm} var Q

    P† : Tm (Ψ ++ []) (A ⊗ B)
    P† = cast (sym (++-idr Ψ)) P

    Cp : Γm ++ (Ψ ++ []) ++ Δm ≡ (Γm ++ []) ++ Ψ ++ Δm
    Cp = flattenᵐ Γm [] Ψ [] Δm ∙ refl

    seg1 : Overᶠ (Γm ++ Ψ ++ Δm) ((Γm ++ []) ++ Ψ ++ Δm) C
             (_∘ᶠ_ {Θ = Γm} {Ξ = Δm} (inc M⊗) (inc P))
             (inc (sub (split-++ʳ Γm here) M⊗ P))
    seg1 = (λ i → ++-idr Γm (~ i) ++ Ψ ++ Δm)
         , λ i → inc (sub (split-here~ʳ Γm (A ⊗ B) Δm i) M⊗ P)

    seg2 : Overᶠ ((Γm ++ []) ++ Ψ ++ Δm) ((Γm ++ []) ++ Ψ ++ Δm) C
             (inc (sub (split-++ʳ Γm here) M⊗ P))
             (inc (cast Cp (match⊗ {Γ = Γm} {Δ = Δm} P† Q)))
    seg2 = refl
         , incᵖ (ap (λ (v : Split-++ Γm ((A ⊗ B) ∷ Δm) (split-++ʳ Γm here))
                       → sub-match⊗ˡ v var Q P)
                    (split-++-ʳ Γm here))

    seg3 : Overᶠ ((Γm ++ []) ++ Ψ ++ Δm) (Γm ++ (Ψ ++ []) ++ Δm) C
             (inc (cast Cp (match⊗ {Γ = Γm} {Δ = Δm} P† Q)))
             (inc (match⊗ {Γ = Γm} {Δ = Δm} P† Q))
    seg3 = sym Cp , incᵖᵖ (symP (cast-filler Cp (match⊗ {Γ = Γm} {Δ = Δm} P† Q)))

    seg4 : Overᶠ (Γm ++ (Ψ ++ []) ++ Δm) (Γm ++ Ψ ++ Δm) C
             (inc (match⊗ {Γ = Γm} {Δ = Δm} P† Q))
             (inc (match⊗ {Γ = Γm} {Δ = Δm} P Q))
    seg4 = (λ i → Γm ++ ++-idr Ψ i ++ Δm)
         , λ i → inc (match⊗ {Γ = Γm} {Δ = Δm}
                        (symP (cast-filler (sym (++-idr Ψ)) P) i) Q)

-- match𝟙 P Q likewise.
decomp-m𝟙 : ∀ {Γm Δm : Ctx} (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C)
          → Overᶠ (Γm ++ Ψ ++ Δm) (Γm ++ Ψ ++ Δm) C
              (_∘ᶠ_ {Θ = Γm} {Ξ = Δm}
                (inc (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Γm} {Δ = Δm} var Q))
                (inc P))
              (inc (match𝟙 {Γ = Γm} {Δ = Δm} P Q))
decomp-m𝟙 {Ψ = Ψ} {C = C} {Γm = Γm} {Δm = Δm} P Q =
  seg1 ∙O seg2 ∙O seg3 ∙O seg4
  where
    M𝟙 : Tm (Γm ++ 𝟙 ∷ Δm) C
    M𝟙 = match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Γm} {Δ = Δm} var Q

    P† : Tm (Ψ ++ []) 𝟙
    P† = cast (sym (++-idr Ψ)) P

    Cp : Γm ++ (Ψ ++ []) ++ Δm ≡ (Γm ++ []) ++ Ψ ++ Δm
    Cp = flattenᵐ Γm [] Ψ [] Δm ∙ refl

    seg1 : Overᶠ (Γm ++ Ψ ++ Δm) ((Γm ++ []) ++ Ψ ++ Δm) C
             (_∘ᶠ_ {Θ = Γm} {Ξ = Δm} (inc M𝟙) (inc P))
             (inc (sub (split-++ʳ Γm here) M𝟙 P))
    seg1 = (λ i → ++-idr Γm (~ i) ++ Ψ ++ Δm)
         , λ i → inc (sub (split-here~ʳ Γm 𝟙 Δm i) M𝟙 P)

    seg2 : Overᶠ ((Γm ++ []) ++ Ψ ++ Δm) ((Γm ++ []) ++ Ψ ++ Δm) C
             (inc (sub (split-++ʳ Γm here) M𝟙 P))
             (inc (cast Cp (match𝟙 {Γ = Γm} {Δ = Δm} P† Q)))
    seg2 = refl
         , incᵖ (ap (λ (v : Split-++ Γm (𝟙 ∷ Δm) (split-++ʳ Γm here))
                       → sub-match𝟙ˡ v var Q P)
                    (split-++-ʳ Γm here))

    seg3 : Overᶠ ((Γm ++ []) ++ Ψ ++ Δm) (Γm ++ (Ψ ++ []) ++ Δm) C
             (inc (cast Cp (match𝟙 {Γ = Γm} {Δ = Δm} P† Q)))
             (inc (match𝟙 {Γ = Γm} {Δ = Δm} P† Q))
    seg3 = sym Cp , incᵖᵖ (symP (cast-filler Cp (match𝟙 {Γ = Γm} {Δ = Δm} P† Q)))

    seg4 : Overᶠ (Γm ++ (Ψ ++ []) ++ Δm) (Γm ++ Ψ ++ Δm) C
             (inc (match𝟙 {Γ = Γm} {Δ = Δm} P† Q))
             (inc (match𝟙 {Γ = Γm} {Δ = Δm} P Q))
    seg4 = (λ i → Γm ++ ++-idr Ψ i ++ Δm)
         , λ i → inc (match𝟙 {Γ = Γm} {Δ = Δm}
                        (symP (cast-filler (sym (++-idr Ψ)) P) i) Q)

-- ==========================================================================
-- Generators.  The padded spine pad As₁ ts — variables for As₁ followed by
-- the entries of ts — lets the generator case recurse on the spine while the
-- already-processed entries turn into variables; gen f sp itself is
-- pad [] sp definitionally.
-- ==========================================================================

pad : ∀ As₁ {Δ₂} {As₂ : List G.Ob} → Sp Δ₂ As₂ → Sp (⟦ As₁ ⟧ᵍ ++ Δ₂) (As₁ ++ As₂)
pad []        ts = ts
pad (A ∷ As₁) ts = _∷_ {Γ = base A ∷ []} var (pad As₁ ts)

-- pad of the empty spine is the identity spine (cons-by-cons).
pad-nil-ctx : ∀ As₁ → ⟦ As₁ ⟧ᵍ ++ [] ≡ ⟦ As₁ ++ [] ⟧ᵍ
pad-nil-ctx []        = refl
pad-nil-ctx (A ∷ As₁) = ap (base A ∷_) (pad-nil-ctx As₁)

pad-nil : ∀ As₁ → PathP (λ i → Sp (pad-nil-ctx As₁ i) (As₁ ++ []))
                    (pad As₁ []) (id-sp (As₁ ++ []))
pad-nil []          = refl
pad-nil (A ∷ As₁) i = _∷_ {Γ = base A ∷ []} var (pad-nil As₁ i)

-- Shifting the leading variable of the tail into the padding prefix.
pad-shift-ctx : ∀ As₁ {A : G.Ob} (Δ₂ : Ctx)
              → ⟦ As₁ ++ A ∷ [] ⟧ᵍ ++ Δ₂ ≡ ⟦ As₁ ⟧ᵍ ++ base A ∷ Δ₂
pad-shift-ctx []         Δ₂ = refl
pad-shift-ctx (A₁ ∷ As₁) Δ₂ = ap (base A₁ ∷_) (pad-shift-ctx As₁ Δ₂)

pad-shift : ∀ As₁ {A : G.Ob} {Δ₂} {As₂ : List G.Ob} (ts₂ : Sp Δ₂ As₂)
          → PathP (λ i → Sp (pad-shift-ctx As₁ {A} Δ₂ i)
                            (++-assoc As₁ (A ∷ []) As₂ i))
              (pad (As₁ ++ A ∷ []) ts₂)
              (pad As₁ (_∷_ {Γ = base A ∷ []} var ts₂))
pad-shift []           ts₂ = refl
pad-shift (A₁ ∷ As₁) ts₂ i = _∷_ {Γ = base A₁ ∷ []} var (pad-shift As₁ ts₂ i)

-- Substituting t for the marked variable behind the padding prefix (the
-- spine-level heart of the generator decomposition).
decomp-sp : ∀ As₁ {A : G.Ob} {Γ₁ Δ' : Ctx} {As₂ : List G.Ob}
            (t : Tm Γ₁ (base A)) (ts₂ : Sp Δ' As₂)
          → OverSp (⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (As₁ ++ A ∷ As₂)
              (sub-sp (split-here ⟦ As₁ ⟧ᵍ (base A) Δ')
                (pad As₁ (_∷_ {Γ = base A ∷ []} var ts₂)) t)
              (pad As₁ (t ∷ ts₂))
decomp-sp [] {A} {Γ₁} {Δ'} {As₂} t ts₂ = seg1 ∙S seg2
  where
    t† : Tm (Γ₁ ++ []) (base A)
    t† = cast (sym (++-idr Γ₁)) t

    c : (Γ₁ ++ []) ++ Δ' ≡ Γ₁ ++ Δ'
    c = flattenˡ [] Γ₁ [] Δ' ∙ refl

    seg1 : OverSp (Γ₁ ++ Δ') ((Γ₁ ++ []) ++ Δ') (A ∷ As₂)
             (sub-sp here (_∷_ {Γ = base A ∷ []} var ts₂) t)
             (t† ∷ ts₂)
    seg1 = sym c , symP (sp-cast-filler c (t† ∷ ts₂))

    seg2 : OverSp ((Γ₁ ++ []) ++ Δ') (Γ₁ ++ Δ') (A ∷ As₂) (t† ∷ ts₂) (t ∷ ts₂)
    seg2 = (λ i → ++-idr Γ₁ i ++ Δ')
         , λ i → symP (cast-filler (sym (++-idr Γ₁)) t) i ∷ ts₂
decomp-sp (A₁ ∷ As₁) {A} {Γ₁} {Δ'} {As₂} t ts₂ = seg1 ∙S seg2
  where
    inner : Sp (⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (As₁ ++ A ∷ As₂)
    inner = sub-sp (split-here ⟦ As₁ ⟧ᵍ (base A) Δ')
              (pad As₁ (_∷_ {Γ = base A ∷ []} var ts₂)) t

    c : base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ' ≡ base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ'
    c = refl ∙ refl

    seg1 : OverSp (base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ')
             (A₁ ∷ As₁ ++ A ∷ As₂)
             (sub-sp (split-here ⟦ A₁ ∷ As₁ ⟧ᵍ (base A) Δ')
               (pad (A₁ ∷ As₁) (_∷_ {Γ = base A ∷ []} var ts₂)) t)
             (_∷_ {Γ = base A₁ ∷ []} var inner)
    seg1 = sym c
         , symP (sp-cast-filler c (_∷_ {Γ = base A₁ ∷ []} var inner))

    seg2 : OverSp (base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (base A₁ ∷ ⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ')
             (A₁ ∷ As₁ ++ A ∷ As₂)
             (_∷_ {Γ = base A₁ ∷ []} var inner)
             (pad (A₁ ∷ As₁) (t ∷ ts₂))
    seg2 = ap (base A₁ ∷_) (decomp-sp As₁ t ts₂ .fst)
         , λ i → _∷_ {Γ = base A₁ ∷ []} var (decomp-sp As₁ t ts₂ .snd i)

-- gen f' over a padded spine, cons step: a ∘ᶠ-composite plugging t into the
-- marked variable (inc/gen applied to decomp-sp under the interval).
decomp-gen : ∀ {B : G.Ob} As₁ {A : G.Ob} {Γ₁ Δ' : Ctx} {As₂ : List G.Ob}
             (f' : G.Hom (As₁ ++ A ∷ As₂) B) (t : Tm Γ₁ (base A)) (ts₂ : Sp Δ' As₂)
           → Overᶠ (⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (⟦ As₁ ⟧ᵍ ++ Γ₁ ++ Δ') (base B)
               (_∘ᶠ_ {Θ = ⟦ As₁ ⟧ᵍ} {Ξ = Δ'}
                 (inc (gen f' (pad As₁ (_∷_ {Γ = base A ∷ []} var ts₂))))
                 (inc t))
               (inc (gen f' (pad As₁ (t ∷ ts₂))))
decomp-gen As₁ f' t ts₂ =
  decomp-sp As₁ t ts₂ .fst , λ i → inc (gen f' (decomp-sp As₁ t ts₂ .snd i))

-- Shift the leading variable of the tail into the prefix, transporting the
-- generator's arity across the structural reassociation.
decomp-shift : ∀ {B : G.Ob} As₁ {A : G.Ob} {Δ₂ : Ctx} {As₂ : List G.Ob}
               (f' : G.Hom (As₁ ++ A ∷ As₂) B) (ts₂ : Sp Δ₂ As₂)
             → Overᶠ (⟦ As₁ ++ A ∷ [] ⟧ᵍ ++ Δ₂) (⟦ As₁ ⟧ᵍ ++ base A ∷ Δ₂) (base B)
                 (inc (gen (subst (λ l → G.Hom l B)
                              (sym (++-assoc As₁ (A ∷ []) As₂)) f')
                        (pad (As₁ ++ A ∷ []) ts₂)))
                 (inc (gen f' (pad As₁ (_∷_ {Γ = base A ∷ []} var ts₂))))
decomp-shift {B = B} As₁ {A} {Δ₂} {As₂} f' ts₂ =
  pad-shift-ctx As₁ Δ₂
  , λ i → inc (gen (symP (transport-filler
                     (λ j → G.Hom (++-assoc As₁ (A ∷ []) As₂ (~ j)) B) f') i)
                (pad-shift As₁ ts₂ i))

-- The empty tail: the padded spine is the generator's identity spine.
decomp-gen-nil : ∀ {B : G.Ob} As₁ (f' : G.Hom (As₁ ++ []) B)
               → Overᶠ ⟦ As₁ ++ [] ⟧ᵍ (⟦ As₁ ⟧ᵍ ++ []) (base B)
                   (inc (generator f'))
                   (inc (gen f' (pad As₁ [])))
decomp-gen-nil As₁ f' =
  sym (pad-nil-ctx As₁) , λ i → inc (gen f' (pad-nil As₁ (~ i)))

-- ==========================================================================
-- The core uniqueness argument: two strict extensions that agree on the
-- generators and on the chosen universal arrows (with universality of the
-- latter) agree on every morphism.
-- ==========================================================================

module Core (F G' : Extension)
  (agree-gen : ∀ {As : List G.Ob} {B : G.Ob} (f : G.Hom As B)
             → Extension.F₁ F (inc (generator f))
             ≡ Extension.F₁ G' (inc (generator f)))
  (agree-⊗ : ∀ (A B : Ty)
           → Extension.F₁ F (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var))
           ≡ Extension.F₁ G' (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)))
  (agree-𝟙 : Extension.F₁ F (inc ⋆) ≡ Extension.F₁ G' (inc ⋆))
  (univ-⊗ : ∀ (A B : Ty)
          → Rep.is-universal M
              (Extension.F₁ G' (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var))))
  (univ-𝟙 : Rep.is-universal M (Extension.F₁ G' (inc ⋆)))
  where

  private
    module F  = Extension F
    module G' = Extension G'

  -- Transfer agreement along a shared decomposition.
  transfer : ∀ {Γ Δ z} {f : Homᶠ Γ z} {g : Homᶠ Δ z}
           → Overᶠ Γ Δ z f g → F.F₁ f ≡ G'.F₁ f → F.F₁ g ≡ G'.F₁ g
  transfer (b , D) e =
    sym (F₁-over F D) ∙ ap (castₘ (ap ⟦_⟧ᶜ b)) e ∙ F₁-over G' D

  -- Agreement is closed under composition (both composition laws run over
  -- the same base, so castₘ-inj cancels it).
  ∘-agree : ∀ {Θ Ξ Γ x z} {f : Homᶠ (Θ ++ x ∷ Ξ) z} {g : Homᶠ Γ x}
          → F.F₁ f ≡ G'.F₁ f → F.F₁ g ≡ G'.F₁ g
          → F.F₁ (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g)
          ≡ G'.F₁ (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘-agree {Θ} {Ξ} {Γ} {x} {z} {f} {g} ef eg = castₘ-inj (⟦⟧-++₂ Θ Γ Ξ)
    ( ∘-hom F f g
    ∙ ap₂ (λ (a : M.Homₘ (⟦ Θ ⟧ᶜ ++ ⟦ x ⟧ᵗ ∷ ⟦ Ξ ⟧ᶜ) ⟦ z ⟧ᵗ)
             (b : M.Homₘ ⟦ Γ ⟧ᶜ ⟦ x ⟧ᵗ)
             → M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ} a b)
        (ap (castₘ (⟦⟧-++ Θ (x ∷ Ξ))) ef) eg
    ∙ sym (∘-hom G' f g) )

  -- Agreement on match⊗ var Q from agreement on Q: both values plug (via
  -- sec⊗ and the composition laws) to the same thing against the common
  -- universal arrow, so they are identified by universality.
  m⊗var-agree : ∀ {Γm Δm A B C} (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
              → F.F₁ (inc Q) ≡ G'.F₁ (inc Q)
              → F.F₁ (inc (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Γm} {Δ = Δm} var Q))
              ≡ G'.F₁ (inc (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Γm} {Δ = Δm} var Q))
  m⊗var-agree {Γm} {Δm} {A} {B} {C} Q eQ =
    castₘ-inj b₂ (Equiv.injective
      ((λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} k vG) , univ-⊗ A B) eq)
    where
      mvQ = inc (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Γm} {Δ = Δm} var Q)
      vv  = inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)
      vG  = G'.F₁ vv
      b₂  = ⟦⟧-++ Γm ((A ⊗ B) ∷ Δm)
      B₂  = ⟦⟧-++₂ Γm (A ∷ B ∷ []) Δm

      secᶠ : _∘ᶠ_ {Θ = Γm} {Ξ = Δm} mvQ vv ≡ inc Q
      secᶠ = quot (sec⊗ {A = A} {B = B} {Θ = Γm} {Ξ = Δm} Q)

      step : (X : Extension)
           → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
               (castₘ b₂ (Extension.F₁ X mvQ)) (Extension.F₁ X vv)
           ≡ castₘ B₂ (Extension.F₁ X (inc Q))
      step X = sym (∘-hom X mvQ vv) ∙ ap (castₘ B₂) (ap (Extension.F₁ X) secᶠ)

      eq : M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (F.F₁ mvQ)) vG
         ≡ M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (G'.F₁ mvQ)) vG
      eq = ap (λ v → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (F.F₁ mvQ)) v)
              (sym (agree-⊗ A B))
         ∙ step F ∙ ap (castₘ B₂) eQ ∙ sym (step G')

  -- Same for match𝟙 var Q via sec𝟙.
  m𝟙var-agree : ∀ {Γm Δm C} (Q : Tm (Γm ++ Δm) C)
              → F.F₁ (inc Q) ≡ G'.F₁ (inc Q)
              → F.F₁ (inc (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Γm} {Δ = Δm} var Q))
              ≡ G'.F₁ (inc (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Γm} {Δ = Δm} var Q))
  m𝟙var-agree {Γm} {Δm} {C} Q eQ =
    castₘ-inj b₂ (Equiv.injective
      ((λ k → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} k vG) , univ-𝟙) eq)
    where
      mvQ = inc (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Γm} {Δ = Δm} var Q)
      vG  = G'.F₁ (inc ⋆)
      b₂  = ⟦⟧-++ Γm (𝟙 ∷ Δm)
      B₂  = ⟦⟧-++₂ Γm [] Δm

      secᶠ : _∘ᶠ_ {Θ = Γm} {Ξ = Δm} mvQ (inc ⋆) ≡ inc Q
      secᶠ = quot (sec𝟙 {Θ = Γm} {Ξ = Δm} Q)

      step : (X : Extension)
           → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ}
               (castₘ b₂ (Extension.F₁ X mvQ)) (Extension.F₁ X (inc ⋆))
           ≡ castₘ B₂ (Extension.F₁ X (inc Q))
      step X = sym (∘-hom X mvQ (inc ⋆))
             ∙ ap (castₘ B₂) (ap (Extension.F₁ X) secᶠ)

      eq : M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (F.F₁ mvQ)) vG
         ≡ M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (G'.F₁ mvQ)) vG
      eq = ap (λ v → M._∘ₘ_ {Θ = ⟦ Γm ⟧ᶜ} {Ξ = ⟦ Δm ⟧ᶜ} (castₘ b₂ (F.F₁ mvQ)) v)
              (sym agree-𝟙)
         ∙ step F ∙ ap (castₘ B₂) eQ ∙ sym (step G')

  -- ========================================================================
  -- The main induction, mutually with the generator-spine recursion (the
  -- padding prefix grows as entries are consumed; termination is structural
  -- on the spine, with unique-tm called on each entry).
  -- ========================================================================

  unique-tm : ∀ {Γ z} (t : Tm Γ z) → F.F₁ (inc t) ≡ G'.F₁ (inc t)
  gen-agree : ∀ {B : G.Ob} As₁ {Δ₂ : Ctx} {As₂ : List G.Ob}
              (f' : G.Hom (As₁ ++ As₂) B) (ts : Sp Δ₂ As₂)
            → F.F₁ (inc (gen f' (pad As₁ ts)))
            ≡ G'.F₁ (inc (gen f' (pad As₁ ts)))

  unique-tm var = F.F-id ∙ sym G'.F-id
  unique-tm (gen f sp) = gen-agree [] f sp
  unique-tm (⦅_,_⦆ {Γ = Γ₁} {A = A} {Δ = Δ₁} {B = B} P Q) =
    transfer (decomp-⊗ P Q)
      (∘-agree {Θ = Γ₁} {Ξ = []}
        (∘-agree {Θ = []} {Ξ = B ∷ []} (agree-⊗ A B) (unique-tm P))
        (unique-tm Q))
  unique-tm (match⊗ {Ψ = Ψ} {A = A} {B = B} {Γ = Γm} {Δ = Δm} P Q) =
    transfer (decomp-m⊗ P Q)
      (∘-agree {Θ = Γm} {Ξ = Δm} (m⊗var-agree Q (unique-tm Q)) (unique-tm P))
  unique-tm ⋆ = agree-𝟙
  unique-tm (match𝟙 {Ψ = Ψ} {Γ = Γm} {Δ = Δm} P Q) =
    transfer (decomp-m𝟙 P Q)
      (∘-agree {Θ = Γm} {Ξ = Δm} (m𝟙var-agree Q (unique-tm Q)) (unique-tm P))

  gen-agree As₁ f' [] = transfer (decomp-gen-nil As₁ f') (agree-gen f')
  gen-agree {B = B} As₁ f' (_∷_ {Γ = Γ₁} {Δ = Δ'} {As = As₂} {A = A} t ts₂) =
    transfer (decomp-gen As₁ f' t ts₂)
      (∘-agree {Θ = ⟦ As₁ ⟧ᵍ} {Ξ = Δ'}
        (transfer (decomp-shift As₁ f' ts₂)
          (gen-agree (As₁ ++ A ∷ [])
            (subst (λ l → G.Hom l B) (sym (++-assoc As₁ (A ∷ []) As₂)) f')
            ts₂))
        (unique-tm t))

  -- Descent to the quotiented hom-sets.
  unique : ∀ {Γ z} (f : Homᶠ Γ z) → F.F₁ f ≡ G'.F₁ f
  unique = Coeq-elim-prop (λ f → M.Homₘ-set (F.F₁ f) (G'.F₁ f)) unique-tm

-- ==========================================================================
-- Instantiation data for the evaluation extension: eval sends the chosen
-- syntactic representability data to M's chosen universal arrows.
-- ==========================================================================

-- eval ⦅var,var⦆ is the binary universal arrow (its cast is over a
-- definitionally-refl boundary, and the two identities cancel by idₘl).
eval-⊗ : ∀ (A B : Ty)
       → evalᶠ (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var))
       ≡ uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])
eval-⊗ A B =
    transport-refl _
  ∙ ap (λ k → M._∘ₘ_ {Θ = ⟦ A ⟧ᵗ ∷ []} {Ξ = []} k M.idₘ)
       (M.idₘl {Θ = []} {Ξ = ⟦ B ⟧ᵗ ∷ []} (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])))
  ∙ M.idₘl {Θ = ⟦ A ⟧ᵗ ∷ []} {Ξ = []} (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []))

-- eval ⋆ is the nullary universal arrow definitionally.
eval-𝟙 : evalᶠ (inc ⋆) ≡ uM []
eval-𝟙 = refl

univ-⊗E : ∀ (A B : Ty)
        → Rep.is-universal M
            (evalᶠ (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)))
univ-⊗E A B = subst (λ u → Rep.is-universal M u) (sym (eval-⊗ A B))
  (uM-universal (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ []))

univ-𝟙E : Rep.is-universal M (evalᶠ (inc ⋆))
univ-𝟙E = uM-universal []

-- ==========================================================================
-- The packaged uniqueness theorem (Shulman, Theorem 2.4.10, uniqueness
-- half): a multifunctor F : FMonCat G → M agreeing with the generators and
-- strictly preserving the chosen representability data equals the
-- evaluation multifunctor, over the pointwise object-agreement paths.
-- ==========================================================================

module _ (F : Multifunctor FMonCat M) where
  private module F = Multifunctor F

  module _
    (agree-ob : ∀ A → F.F₀ A ≡ ⟦ A ⟧ᵗ)
    (agree-gen : ∀ {As : List G.Ob} {B : G.Ob} (f : G.Hom As B)
               → PathP (λ i → M.Homₘ (map (λ A → agree-ob A i) ⟦ As ⟧ᵍ)
                                      (agree-ob (base B) i))
                   (F.F₁ (inc (generator f))) (eval (generator f)))
    (agree-⊗ : ∀ (A B : Ty)
             → PathP (λ i → M.Homₘ (agree-ob A i ∷ agree-ob B i ∷ [])
                                    (agree-ob (A ⊗ B) i))
                 (F.F₁ (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var)))
                 (uM (⟦ A ⟧ᵗ ∷ ⟦ B ⟧ᵗ ∷ [])))
    (agree-𝟙 : PathP (λ i → M.Homₘ [] (agree-ob 𝟙 i))
                 (F.F₁ (inc ⋆)) (uM []))
    where

    private
      mp : (Γ : Ctx) → map F.F₀ Γ ≡ ⟦ Γ ⟧ᶜ
      mp Γ i = map (λ A → agree-ob A i) Γ

      -- F, transported onto the strict object part ⟦_⟧ᵗ.
      F₁' : ∀ {Γ z} → Homᶠ Γ z → M.Homₘ ⟦ Γ ⟧ᶜ ⟦ z ⟧ᵗ
      F₁' {Γ} {z} f =
        transport (λ i → M.Homₘ (mp Γ i) (agree-ob z i)) (F.F₁ f)

      F₁'-filler : ∀ {Γ z} (f : Homᶠ Γ z)
                 → PathP (λ i → M.Homₘ (mp Γ i) (agree-ob z i))
                     (F.F₁ f) (F₁' f)
      F₁'-filler {Γ} {z} f =
        transport-filler (λ i → M.Homₘ (mp Γ i) (agree-ob z i)) (F.F₁ f)

      F'-id : ∀ {z} → F₁' (idᶠ {z}) ≡ M.idₘ
      F'-id {z} =
        ap (transport (λ i → M.Homₘ (agree-ob z i ∷ []) (agree-ob z i))) F.F-idₘ
        ∙ from-pathp (λ i → M.idₘ {agree-ob z i})

      -- F's composition law, conjugated by the transport fillers: the
      -- missing face of the square whose cap is F.F-∘ₘ and whose sides are
      -- the fillers (with the inner castₘ varying along the agreement).
      F'-∘ : ∀ {Θ Ξ Γ x z} (f : Homᶠ (Θ ++ x ∷ Ξ) z) (g : Homᶠ Γ x)
           → PathP (λ j → M.Homₘ (⟦⟧-++₂ Θ Γ Ξ j) ⟦ z ⟧ᵗ)
               (F₁' (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g))
               (M._∘ₘ_ {Θ = ⟦ Θ ⟧ᶜ} {Ξ = ⟦ Ξ ⟧ᶜ}
                 (castₘ (⟦⟧-++ Θ (x ∷ Ξ)) (F₁' f)) (F₁' g))
      F'-∘ {Θ} {Ξ} {Γ} {x} {z} f g j =
        comp (λ i → M.Homₘ (map-++₂ (λ A → agree-ob A i) Θ Γ Ξ j)
                           (agree-ob z i))
             (∂ j) λ where
          i (i = i0) → F.F-∘ₘ {Θ = Θ} {Ξ = Ξ} f g j
          i (j = i0) → F₁'-filler (_∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f g) i
          i (j = i1) →
            M._∘ₘ_ {Θ = map (λ A → agree-ob A i) Θ}
                   {Ξ = map (λ A → agree-ob A i) Ξ}
              (castₘ (map-++ (λ A → agree-ob A i) Θ (x ∷ Ξ)) (F₁'-filler f i))
              (F₁'-filler g i)

      F' : Extension
      F' .Extension.F₁ = F₁'
      F' .Extension.F-id = F'-id
      F' .Extension.F-∘ = F'-∘

      -- The agreement data, homogenised onto F'.
      agree-gen' : ∀ {As : List G.Ob} {B : G.Ob} (f : G.Hom As B)
                 → F₁' (inc (generator f)) ≡ evalᶠ (inc (generator f))
      agree-gen' f = from-pathp (agree-gen f)

      agree-⊗' : ∀ (A B : Ty)
               → F₁' (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var))
               ≡ evalᶠ (inc (⦅_,_⦆ {Γ = A ∷ []} {Δ = B ∷ []} var var))
      agree-⊗' A B = from-pathp (agree-⊗ A B) ∙ sym (eval-⊗ A B)

      agree-𝟙' : F₁' (inc ⋆) ≡ evalᶠ (inc ⋆)
      agree-𝟙' = from-pathp agree-𝟙

      module U = Core F' Eval-ext agree-gen' agree-⊗' agree-𝟙' univ-⊗E univ-𝟙E

    -- The theorem: F is the evaluation multifunctor, over agree-ob.
    uniqueness : ∀ {Γ z} (f : Homᶠ Γ z)
               → PathP (λ i → M.Homₘ (map (λ A → agree-ob A i) Γ)
                                     (agree-ob z i))
                   (F.F₁ f) (evalᶠ f)
    uniqueness f = F₁'-filler f ▷ U.unique f
