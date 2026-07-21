open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso; Hom-transport)
open import Cat.Functor.Naturality
import Cat.Functor.Base as FB
import Cat.Bi.Reasoning
import Cat.Bi.Solver
open import Data.List
open import Data.List.Properties

module Multicategory.Representable where

-- The representable multicategory of a monoidal category.
--
-- A multimorphism Γ ⟶ τ is a unary morphism (⊗ Γ) ⟶ τ in C, where ⊗ Γ
-- right-associates the tensor product over the (list) context and the empty
-- context is the tensor unit.  Because contexts are lists, ⊗-context is a plain
-- fold that reduces through _++_ definitionally — so the rebracketing isos used
-- in composition are reducing, and the law boundaries (plain list ≡s) are seen
-- through by ⊗-context.  This is what makes the laws tractable here, where they
-- were blocked in the Vec-based version.
representable-multicategory
  : ∀ {o h} (C : Precategory o h) → Monoidal-category C → Premulticategory o h
representable-multicategory C M = Mc where
  open Cr C
  open Monoidal-category M
  open Premulticategory

  -- The monoidal coherence lemmas we need live in Cat.Bi.Reasoning; via the
  -- delooping they specialise to object-level facts about C.  In the delooping,
  -- 1-cells are objects of C and the 1-cell tensor is the monoidal ⊗, so the
  -- bicategory's ρ←/λ←/α← (and ▶/◀/⊗) are definitionally the monoidal ones.
  open Cat.Bi.Reasoning (Deloop M) using
    (triangle-ρ→ ; triangle-λ← ; λ→≡ρ→ ; ▶-assoc ; ◀-▶-comm ; ◀-assoc
    ; λ→nat ; λ←nat ; ρ←nat)

  ⊗-context : List Ob → Ob
  ⊗-context []       = Unit
  ⊗-context (x ∷ Γ)  = x ⊗ ⊗-context Γ

  -- Tensor of a concatenation splits into the tensors of the parts; reducing.
  ⊗-context-++ : (Γ Δ : List Ob)
    → ⊗-context (Γ ++ Δ) ≅ (⊗-context Γ ⊗ ⊗-context Δ)
  ⊗-context-++ []      Δ = λ≅
  ⊗-context-++ (x ∷ Γ) Δ = ▶.F-map-iso (⊗-context-++ Γ Δ) ∙Iso (α≅ Iso⁻¹)

  -- Three-way split.
  ⊗-context-++-++ : (A B C : List Ob)
    → ⊗-context (A ++ B ++ C) ≅ (⊗-context A ⊗ (⊗-context B ⊗ ⊗-context C))
  ⊗-context-++-++ A B C =
    ⊗-context-++ A (B ++ C) ∙Iso ▶.F-map-iso (⊗-context-++ B C)

  -- path→iso of a refl path is id-iso.
  path→iso-refl : ∀ {A : Ob} → path→iso (refl {x = A}) ≡ id-iso
  path→iso-refl = transport-refl _

  -- path→iso sees through tensoring-on-the-left (Cat.Functor.Base.F-iso).
  path→iso-ap-⊗ : ∀ x {A B : Ob} (p : A ≡ B)
    → path→iso (ap (λ Y → x ⊗ Y) p) ≡ ▶.F-map-iso (path→iso p)
  path→iso-ap-⊗ x p = ap-F₀-to-iso p
    where open FB.F-iso (-⊗-.Right x)

  -- Transporting a morphism along an object path (fixed codomain) is
  -- precomposition with the induced iso.  Every law uses this to discharge the
  -- to-pathp obligation; the `subst`-over-⊗-context form composes it with a
  -- path→iso characterisation.
  transport-⊗-red : ∀ {z} {A B : Ob} (q : A ≡ B) (m : Hom A z)
    → transport (λ i → Hom (q i) z) m ≡ m ∘ path→iso q .from
  transport-⊗-red q m =
      Hom-transport C q refl m
    ∙ ap (λ k → k ∘ m ∘ path→iso q .from) (ap (λ i → i .to) path→iso-refl)
    ∙ idl _

  subst-⊗-red : ∀ {z} {A B : List Ob} (p : A ≡ B) {i : _ ≅ _}
    → path→iso (ap ⊗-context p) ≡ i → (m : Hom (⊗-context A) z)
    → subst (λ Ω → Hom (⊗-context Ω) z) p m ≡ m ∘ i .from
  subst-⊗-red p char m =
    transport-⊗-red (ap ⊗-context p) m ∙ ap (m ∘_) (ap (λ i → i .from) char)

  -- ⊗(Γ ++ []) ≅ ⊗Γ, mirroring ++-idr's recursion (id at [], ▶ at cons).
  -- Stated this way so path→iso of the ++-idr boundary equals it by a clean
  -- induction (no ρ/α coherence chase) — see ⊗-context-++-idr-path.
  ⊗-context-++-idr : (Γ : List Ob) → ⊗-context (Γ ++ []) ≅ ⊗-context Γ
  ⊗-context-++-idr []      = id-iso
  ⊗-context-++-idr (x ∷ Γ) = ▶.F-map-iso (⊗-context-++-idr Γ)

  -- The ++-idr boundary induces exactly ⊗-context-++-idr.
  ⊗-context-++-idr-path : (Γ : List Ob)
    → path→iso (ap ⊗-context (++-idr Γ)) ≡ ⊗-context-++-idr Γ
  ⊗-context-++-idr-path []      = path→iso-refl
  ⊗-context-++-idr-path (x ∷ Γ) =
      path→iso-ap-⊗ x (ap ⊗-context (++-idr Γ))
    ∙ ap ▶.F-map-iso (⊗-context-++-idr-path Γ)

  -- Appending the empty summand on the right of the split is exactly the right
  -- unitor ρ→ on ⊗Γ: (⊗-context-++ Γ []).to ∘ (⊗-context-++-idr Γ).from = ρ→.
  -- The empty right-summand introduces a trailing unit, which ρ→ inserts.
  -- Proven cons-by-cons so the iso projections reduce; the step is the
  -- monoidal coherence triangle-ρ→ (the inverse direction), the base the unit
  -- coherence λ→≡ρ→.
  ⊗-context-++-[]-ρ : (Γ : List Ob)
    → (⊗-context-++ Γ []) .to ∘ (⊗-context-++-idr Γ) .from ≡ ρ→ (⊗-context Γ)
  ⊗-context-++-[]-ρ []      = idr _ ∙ λ→≡ρ→
  ⊗-context-++-[]-ρ (x ∷ Γ) =
      (⊗-context-++ (x ∷ Γ) []) .to ∘ (⊗-context-++-idr (x ∷ Γ)) .from
    ≡⟨⟩
      (α← _ ∘ (x ▶ (⊗-context-++ Γ []) .to)) ∘ (x ▶ (⊗-context-++-idr Γ) .from)
    ≡⟨ sym (assoc _ _ _) ⟩
      α← _ ∘ ((x ▶ (⊗-context-++ Γ []) .to) ∘ (x ▶ (⊗-context-++-idr Γ) .from))
    ≡⟨ ap (α← _ ∘_) (sym (▶.F-∘ _ _)) ⟩
      α← _ ∘ (x ▶ ((⊗-context-++ Γ []) .to ∘ (⊗-context-++-idr Γ) .from))
    ≡⟨ ap (α← _ ∘_) (ap (x ▶_) (⊗-context-++-[]-ρ Γ)) ⟩
      α← _ ∘ (x ▶ ρ→ (⊗-context Γ))
    ≡⟨ sym triangle-ρ→ ⟩
      ρ→ (x ⊗ ⊗-context Γ)
    ∎

  -- path→iso (ap ⊗-context (++-assoc Φ Ψ Ξ)) is the cons-by-cons ▶-chain
  -- (an instance of ⊗-context being invariant under list reassociation).
  ++-assoc-⊗-iso : (Φ Ψ Ξ : List Ob)
    → ⊗-context ((Φ ++ Ψ) ++ Ξ) ≅ ⊗-context (Φ ++ (Ψ ++ Ξ))
  ++-assoc-⊗-iso []      Ψ Ξ = id-iso
  ++-assoc-⊗-iso (a ∷ Φ) Ψ Ξ = ▶.F-map-iso (++-assoc-⊗-iso Φ Ψ Ξ)

  ++-assoc-⊗-path : (Φ Ψ Ξ : List Ob)
    → path→iso (ap ⊗-context (++-assoc Φ Ψ Ξ)) ≡ ++-assoc-⊗-iso Φ Ψ Ξ
  ++-assoc-⊗-path []      Ψ Ξ = path→iso-refl
  ++-assoc-⊗-path (a ∷ Φ) Ψ Ξ =
      path→iso-ap-⊗ a (ap ⊗-context (++-assoc Φ Ψ Ξ))
    ∙ ap ▶.F-map-iso (++-assoc-⊗-path Φ Ψ Ξ)

  -- path→iso (ap ⊗-context (slot-unbury Θ Φ y Ψ Ξ)): relocating the marked
  -- slot from Φ into (Θ++Φ) is a ▶-chain (over Θ and Φ) of the ++-assoc iso.
  slot-unbury-iso : (Θ Φ : List Ob) (y : Ob) (Ψ Ξ : List Ob)
    → ⊗-context (Θ ++ ((Φ ++ y ∷ Ψ) ++ Ξ)) ≅ ⊗-context ((Θ ++ Φ) ++ y ∷ (Ψ ++ Ξ))
  slot-unbury-iso []      Φ y Ψ Ξ = ++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ
  slot-unbury-iso (a ∷ Θ) Φ y Ψ Ξ = ▶.F-map-iso (slot-unbury-iso Θ Φ y Ψ Ξ)

  slot-unbury-⊗ : (Θ Φ : List Ob) (y : Ob) (Ψ Ξ : List Ob)
    → path→iso (ap ⊗-context (slot-unbury Θ Φ y Ψ Ξ)) ≡ slot-unbury-iso Θ Φ y Ψ Ξ
  slot-unbury-⊗ []      Φ y Ψ Ξ = ++-assoc-⊗-path Φ (y ∷ Ψ) Ξ
  slot-unbury-⊗ (a ∷ Θ) Φ y Ψ Ξ =
      path→iso-ap-⊗ a (ap ⊗-context (slot-unbury Θ Φ y Ψ Ξ))
    ∙ ap ▶.F-map-iso (slot-unbury-⊗ Θ Φ y Ψ Ξ)

  -- path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)).
  assocₘ-flatten-iso : (Φ Ρ Ψ Ξ : List Ob)
    → ⊗-context (Φ ++ Ρ ++ (Ψ ++ Ξ)) ≅ ⊗-context ((Φ ++ Ρ ++ Ψ) ++ Ξ)
  assocₘ-flatten-iso []      []      Ψ Ξ = id-iso
  assocₘ-flatten-iso []      (b ∷ Ρ) Ψ Ξ = ▶.F-map-iso (assocₘ-flatten-iso [] Ρ Ψ Ξ)
  assocₘ-flatten-iso (a ∷ Φ) Ρ       Ψ Ξ = ▶.F-map-iso (assocₘ-flatten-iso Φ Ρ Ψ Ξ)

  assocₘ-flatten-⊗ : (Φ Ρ Ψ Ξ : List Ob)
    → path→iso (ap ⊗-context (assocₘ-flatten Φ Ρ Ψ Ξ)) ≡ assocₘ-flatten-iso Φ Ρ Ψ Ξ
  assocₘ-flatten-⊗ []      []      Ψ Ξ = path→iso-refl
  assocₘ-flatten-⊗ []      (b ∷ Ρ) Ψ Ξ =
      path→iso-ap-⊗ b (ap ⊗-context (assocₘ-flatten [] Ρ Ψ Ξ))
    ∙ ap ▶.F-map-iso (assocₘ-flatten-⊗ [] Ρ Ψ Ξ)
  assocₘ-flatten-⊗ (a ∷ Φ) Ρ       Ψ Ξ =
      path→iso-ap-⊗ a (ap ⊗-context (assocₘ-flatten Φ Ρ Ψ Ξ))
    ∙ ap ▶.F-map-iso (assocₘ-flatten-⊗ Φ Ρ Ψ Ξ)

  assocₘ-boundary-iso : (Θ Φ Ρ Ψ Ξ : List Ob)
    → ⊗-context ((Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ)) ≅ ⊗-context (Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ))
  assocₘ-boundary-iso []      Φ Ρ Ψ Ξ = assocₘ-flatten-iso Φ Ρ Ψ Ξ
  assocₘ-boundary-iso (a ∷ Θ) Φ Ρ Ψ Ξ = ▶.F-map-iso (assocₘ-boundary-iso Θ Φ Ρ Ψ Ξ)

  assocₘ-boundary-⊗ : (Θ Φ Ρ Ψ Ξ : List Ob)
    → path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)) ≡ assocₘ-boundary-iso Θ Φ Ρ Ψ Ξ
  assocₘ-boundary-⊗ []      Φ Ρ Ψ Ξ = assocₘ-flatten-⊗ Φ Ρ Ψ Ξ
  assocₘ-boundary-⊗ (a ∷ Θ) Φ Ρ Ψ Ξ =
      path→iso-ap-⊗ a (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ))
    ∙ ap ▶.F-map-iso (assocₘ-boundary-⊗ Θ Φ Ρ Ψ Ξ)

  ----------------------------------------------------------------------
  -- interchangeₘ path→iso characterisations (cons-by-cons ▶-chains, mirroring
  -- the assocₘ ones).  f has two slots x,y: Θ ++ x ∷ Μ ++ y ∷ Κ.
  ----------------------------------------------------------------------

  -- interchange-slot₀ : Θ ++ x ∷ Μ ++ y ∷ Κ ≡ (Θ ++ x ∷ Μ) ++ y ∷ Κ  (expose y)
  ic-slot₀-iso : (Θ : List Ob) (x : Ob) (Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-context (Θ ++ x ∷ Μ ++ y ∷ Κ) ≅ ⊗-context ((Θ ++ x ∷ Μ) ++ y ∷ Κ)
  ic-slot₀-iso []      x Μ y Κ = id-iso
  ic-slot₀-iso (a ∷ Θ) x Μ y Κ = ▶.F-map-iso (ic-slot₀-iso Θ x Μ y Κ)

  ic-slot₀-⊗ : (Θ : List Ob) (x : Ob) (Μ : List Ob) (y : Ob) (Κ : List Ob)
    → path→iso (ap ⊗-context (interchange-slot₀ Θ x Μ y Κ)) ≡ ic-slot₀-iso Θ x Μ y Κ
  ic-slot₀-⊗ []      x Μ y Κ = path→iso-refl
  ic-slot₀-⊗ (a ∷ Θ) x Μ y Κ =
      path→iso-ap-⊗ a (ap ⊗-context (interchange-slot₀ Θ x Μ y Κ))
    ∙ ap ▶.F-map-iso (ic-slot₀-⊗ Θ x Μ y Κ)

  -- interchange-slot₂ : (Θ ++ x ∷ Μ) ++ Δ ++ Κ ≡ Θ ++ x ∷ (Μ ++ Δ ++ Κ)
  ic-slot₂-iso : (Θ : List Ob) (x : Ob) (Μ Δ Κ : List Ob)
    → ⊗-context ((Θ ++ x ∷ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Θ ++ x ∷ (Μ ++ Δ ++ Κ))
  ic-slot₂-iso []      x Μ Δ Κ = id-iso
  ic-slot₂-iso (a ∷ Θ) x Μ Δ Κ = ▶.F-map-iso (ic-slot₂-iso Θ x Μ Δ Κ)

  ic-slot₂-⊗ : (Θ : List Ob) (x : Ob) (Μ Δ Κ : List Ob)
    → path→iso (ap ⊗-context (interchange-slot₂ Θ x Μ Δ Κ)) ≡ ic-slot₂-iso Θ x Μ Δ Κ
  ic-slot₂-⊗ []      x Μ Δ Κ = path→iso-refl
  ic-slot₂-⊗ (a ∷ Θ) x Μ Δ Κ =
      path→iso-ap-⊗ a (ap ⊗-context (interchange-slot₂ Θ x Μ Δ Κ))
    ∙ ap ▶.F-map-iso (ic-slot₂-⊗ Θ x Μ Δ Κ)

  -- interchange-flatten : (Γ ++ Μ) ++ Δ ++ Κ ≡ Γ ++ (Μ ++ Δ ++ Κ)
  ic-flatten-iso : (Γ Μ Δ Κ : List Ob)
    → ⊗-context ((Γ ++ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Γ ++ (Μ ++ Δ ++ Κ))
  ic-flatten-iso []      Μ Δ Κ = id-iso
  ic-flatten-iso (a ∷ Γ) Μ Δ Κ = ▶.F-map-iso (ic-flatten-iso Γ Μ Δ Κ)

  ic-flatten-⊗ : (Γ Μ Δ Κ : List Ob)
    → path→iso (ap ⊗-context (interchange-flatten Γ Μ Δ Κ)) ≡ ic-flatten-iso Γ Μ Δ Κ
  ic-flatten-⊗ []      Μ Δ Κ = path→iso-refl
  ic-flatten-⊗ (a ∷ Γ) Μ Δ Κ =
      path→iso-ap-⊗ a (ap ⊗-context (interchange-flatten Γ Μ Δ Κ))
    ∙ ap ▶.F-map-iso (ic-flatten-⊗ Γ Μ Δ Κ)

  -- interchangeₘ-boundary : (Θ ++ Γ ++ Μ) ++ Δ ++ Κ ≡ Θ ++ Γ ++ (Μ ++ Δ ++ Κ)
  ic-boundary-iso : (Θ Γ Μ Δ Κ : List Ob)
    → ⊗-context ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Θ ++ Γ ++ (Μ ++ Δ ++ Κ))
  ic-boundary-iso []      Γ Μ Δ Κ = ic-flatten-iso Γ Μ Δ Κ
  ic-boundary-iso (a ∷ Θ) Γ Μ Δ Κ = ▶.F-map-iso (ic-boundary-iso Θ Γ Μ Δ Κ)

  ic-boundary-⊗ : (Θ Γ Μ Δ Κ : List Ob)
    → path→iso (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ)) ≡ ic-boundary-iso Θ Γ Μ Δ Κ
  ic-boundary-⊗ []      Γ Μ Δ Κ = ic-flatten-⊗ Γ Μ Δ Κ
  ic-boundary-⊗ (a ∷ Θ) Γ Μ Δ Κ =
      path→iso-ap-⊗ a (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ))
    ∙ ap ▶.F-map-iso (ic-boundary-⊗ Θ Γ Μ Δ Κ)

  -- interchange-slot₁ : Θ ++ Γ ++ Μ ++ y ∷ Κ ≡ (Θ ++ Γ ++ Μ) ++ y ∷ Κ
  -- (double induction on Θ then Γ, since the [] base is sym (++-assoc Γ Μ (y ∷ Κ))).
  ic-slot₁-iso : (Θ Γ Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-context (Θ ++ Γ ++ Μ ++ y ∷ Κ) ≅ ⊗-context ((Θ ++ Γ ++ Μ) ++ y ∷ Κ)
  ic-slot₁-iso []      []      Μ y Κ = id-iso
  ic-slot₁-iso []      (b ∷ Γ) Μ y Κ = ▶.F-map-iso (ic-slot₁-iso [] Γ Μ y Κ)
  ic-slot₁-iso (a ∷ Θ) Γ       Μ y Κ = ▶.F-map-iso (ic-slot₁-iso Θ Γ Μ y Κ)

  ic-slot₁-⊗ : (Θ Γ Μ : List Ob) (y : Ob) (Κ : List Ob)
    → path→iso (ap ⊗-context (interchange-slot₁ Θ Γ Μ y Κ)) ≡ ic-slot₁-iso Θ Γ Μ y Κ
  ic-slot₁-⊗ []      []      Μ y Κ = path→iso-refl
  ic-slot₁-⊗ []      (b ∷ Γ) Μ y Κ =
      path→iso-ap-⊗ b (ap ⊗-context (interchange-slot₁ [] Γ Μ y Κ))
    ∙ ap ▶.F-map-iso (ic-slot₁-⊗ [] Γ Μ y Κ)
  ic-slot₁-⊗ (a ∷ Θ) Γ Μ y Κ =
      path→iso-ap-⊗ a (ap ⊗-context (interchange-slot₁ Θ Γ Μ y Κ))
    ∙ ap ▶.F-map-iso (ic-slot₁-⊗ Θ Γ Μ y Κ)

  -- Plug g into the slot x of f's domain: rebracket ⊗(Θ ++ Γ ++ Ξ) so that ⊗Γ
  -- sits where x was, apply g there (whiskered with identities), and rebracket
  -- back to ⊗(Θ ++ x ∷ Ξ).  Composition is then f ∘ plug.
  plug : ∀ {x} (Θ Γ Ξ : List Ob)
    → Hom (⊗-context Γ) x
    → Hom (⊗-context (Θ ++ Γ ++ Ξ)) (⊗-context (Θ ++ x ∷ Ξ))
  plug {x} Θ Γ Ξ g =
        (⊗-context-++ Θ (x ∷ Ξ)) .from
    ∘   (⊗-context Θ ▶ (g ◀ ⊗-context Ξ))
    ∘   (⊗-context-++-++ Θ Γ Ξ) .to

  -- Prepending an object a to the prefix tensors the 3-way split on the left,
  -- up to the associator (α← moves the new a⊗ past the split).  Used to run the
  -- assocₘ h-coherence (g-free/plug-assoc) by induction on the prefix.
  split3-cons : (a : Ob) (Ω B Ξ' : List Ob)
    → (⊗-context-++-++ (a ∷ Ω) B Ξ') .to
      ≡ α← (a , ⊗-context Ω , ⊗-context B ⊗ ⊗-context Ξ')
        ∘ (a ▶ (⊗-context-++-++ Ω B Ξ') .to)
  split3-cons a Ω B Ξ' =
      assoc _ _ _
    ∙ ap (_∘ (a ▶ (⊗-context-++ Ω (B ++ Ξ')) .to))
         (sym ((▶-assoc {f = a} {g = ⊗-context Ω}) .Isoⁿ.from .is-natural _ _ ((⊗-context-++ B Ξ') .to)))
    ∙ sym (assoc _ _ _)
    ∙ ap (α← (a , ⊗-context Ω , ⊗-context B ⊗ ⊗-context Ξ') ∘_) (sym (▶.F-∘ _ _))

  -- Prepending an object to the prefix simply tensors the whole plug on the
  -- left: plug (a ∷ Ω) Γ Ξ' g = a ▶ plug Ω Γ Ξ' g.  The α→'s from the head
  -- (φ) and the α←'s from the tail (dec) cancel around the whiskered middle
  -- (slid across by ▶-assoc naturality).
  plug-cons : ∀ {x} (a : Ob) (Ω Γ Ξ' : List Ob) (g : Hom (⊗-context Γ) x)
    → plug (a ∷ Ω) Γ Ξ' g ≡ a ▶ plug Ω Γ Ξ' g
  plug-cons {x} a Ω Γ Ξ' g =
      plug (a ∷ Ω) Γ Ξ' g
    ≡⟨ ap (λ z → ((a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from) ∘ α→ (a , ⊗-context Ω , x ⊗ ⊗-context Ξ'))
               ∘ ((a ⊗ ⊗-context Ω) ▶ (g ◀ ⊗-context Ξ')) ∘ z)
          (split3-cons a Ω Γ Ξ') ⟩
      ((a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from) ∘ α→ (a , ⊗-context Ω , x ⊗ ⊗-context Ξ'))
        ∘ ((a ⊗ ⊗-context Ω) ▶ (g ◀ ⊗-context Ξ'))
        ∘ (α← (a , ⊗-context Ω , ⊗-context Γ ⊗ ⊗-context Ξ') ∘ (a ▶ (⊗-context-++-++ Ω Γ Ξ') .to))
    ≡⟨ sym (assoc _ _ _)
     ∙ ap ((a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from) ∘_)
          ( extendl ((▶-assoc {f = a} {g = ⊗-context Ω}) .Isoⁿ.to .is-natural _ _ (g ◀ ⊗-context Ξ'))
          ∙ ap ((a ▶ (⊗-context Ω ▶ (g ◀ ⊗-context Ξ'))) ∘_) (cancell (α≅ .invl)) ) ⟩
      (a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from)
        ∘ ((a ▶ (⊗-context Ω ▶ (g ◀ ⊗-context Ξ'))) ∘ (a ▶ (⊗-context-++-++ Ω Γ Ξ') .to))
    ≡⟨ ap ((a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from) ∘_) (sym (▶.F-∘ _ _)) ⟩
      (a ▶ (⊗-context-++ Ω (x ∷ Ξ')) .from)
        ∘ (a ▶ ((⊗-context Ω ▶ (g ◀ ⊗-context Ξ')) ∘ (⊗-context-++-++ Ω Γ Ξ') .to))
    ≡⟨ sym (▶.F-∘ _ _) ⟩
      a ▶ plug Ω Γ Ξ' g
    ∎

  -- With no prefix the 3-way split is the 2-way split up to the left unitor.
  split3-nil : (B Ξ' : List Ob)
    → (⊗-context-++-++ [] B Ξ') .to
      ≡ λ→ (⊗-context B ⊗ ⊗-context Ξ') ∘ (⊗-context-++ B Ξ') .to
  split3-nil B Ξ' = sym (λ→nat ((⊗-context-++ B Ξ') .to))

  -- With no prefix, plug is just the whiskered morphism after the 2-way split.
  plug-nil : ∀ {x} (Γ Ξ' : List Ob) (g : Hom (⊗-context Γ) x)
    → plug [] Γ Ξ' g ≡ (g ◀ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to
  plug-nil {x} Γ Ξ' g =
      plug [] Γ Ξ' g
    ≡⟨ ap (λ z → λ← (x ⊗ ⊗-context Ξ') ∘ (Unit ▶ (g ◀ ⊗-context Ξ')) ∘ z) (split3-nil Γ Ξ') ⟩
      λ← (x ⊗ ⊗-context Ξ')
        ∘ ((Unit ▶ (g ◀ ⊗-context Ξ')) ∘ (λ→ (⊗-context Γ ⊗ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to))
    ≡⟨ extendl (λ←nat (g ◀ ⊗-context Ξ')) ⟩
      (g ◀ ⊗-context Ξ')
        ∘ (λ← (⊗-context Γ ⊗ ⊗-context Ξ') ∘ (λ→ (⊗-context Γ ⊗ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to))
    ≡⟨ ap ((g ◀ ⊗-context Ξ') ∘_) (cancell (λ≅ .invr)) ⟩
      (g ◀ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to
    ∎

  -- At empty prefix, assocₘ-flatten's .from is ++-assoc's .to (same direction,
  -- ⊗((Ρ++Ψ)++Ξ) → ⊗(Ρ++(Ψ++Ξ)); the isos themselves are mutual inverses).
  flat-from : (Ρ Ψ Ξ' : List Ob)
    → (assocₘ-flatten-iso [] Ρ Ψ Ξ') .from ≡ (++-assoc-⊗-iso Ρ Ψ Ξ') .to
  flat-from []      Ψ Ξ' = refl
  flat-from (b ∷ Ρ) Ψ Ξ' = ap (b ▶_) (flat-from Ρ Ψ Ξ')

  ----------------------------------------------------------------------
  -- The monoidal-functor associativity hexagon for ⊗-context, stated
  -- standalone (the substance of "⊗-context is a strong monoidal functor").
  --   φ_{Γ,Δ} = (⊗-context-++ Γ Δ).from : ⊗Γ ⊗ ⊗Δ → ⊗(Γ++Δ)
  --   F-α→ : the associativity coherence (pure iso, no f/g/h).
  ----------------------------------------------------------------------
  φ : (Γ Δ : List Ob) → Hom (⊗-context Γ ⊗ ⊗-context Δ) (⊗-context (Γ ++ Δ))
  φ Γ Δ = (⊗-context-++ Γ Δ) .from

  -- Cons-reduction of φ (definitional, hence refl):
  --   φ (a ∷ Γ) Δ  =  (a ▶ φ Γ Δ) ∘ α→ (a , ⊗Γ , ⊗Δ)
  φ-cons : (a : Ob) (Γ Δ : List Ob)
    → φ (a ∷ Γ) Δ ≡ (a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , ⊗-context Δ)
  φ-cons a Γ Δ = refl

  F-α→ : (Γ Δ Ξ : List Ob)
    →   ++-assoc-⊗-iso Γ Δ Ξ .to  ∘ φ (Γ ++ Δ) Ξ ∘ (φ Γ Δ ◀ ⊗-context Ξ)
    ≡ φ Γ (Δ ++ Ξ) ∘ (⊗-context Γ ▶ φ Δ Ξ) ∘ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
  F-α→ [] Δ Ξ =
      idl _
    ∙ ap (φ Δ Ξ ∘_) (sym triangle-λ←)
    ∙ assoc _ _ _
    ∙ ap (λ x → x ∘ α→ (Unit , ⊗-context Δ , ⊗-context Ξ))
          (sym (λ←nat (φ Δ Ξ)))
    ∙ sym (assoc _ _ _)
  F-α→ (a ∷ Γ) Δ Ξ =
        ++-assoc-⊗-iso (a ∷ Γ) Δ Ξ .to ∘ φ ((a ∷ Γ) ++ Δ) Ξ ∘ (φ (a ∷ Γ) Δ ◀ ⊗-context Ξ)
      ≡⟨⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ ((a ▶ φ (Γ ++ Δ) Ξ) ∘ α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ))
      ∘ (((a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , ⊗-context Δ)) ◀ ⊗-context Ξ)
      -- coh1: distribute ◀ over the whiskered α2, use ◀-▶-comm (middle-slot α→
      -- naturality) to push φ Γ Δ past the outer α→, then merge the ▶-layer.
      -- No IH — pure structure.
      ≡⟨ ap (λ z → (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
                 ∘ ((a ▶ φ (Γ ++ Δ) Ξ) ∘ α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ)) ∘ z)
            (◀.F-∘ _ _) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ ((a ▶ φ (Γ ++ Δ) Ξ) ∘ α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ))
      ∘ (((a ▶ φ Γ Δ) ◀ ⊗-context Ξ) ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ))
      ≡⟨ ap ((a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘_)
            (sym (assoc _ _ _) ∙ ap ((a ▶ φ (Γ ++ Δ) Ξ) ∘_) (assoc _ _ _)) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ (a ▶ φ (Γ ++ Δ) Ξ)
      ∘ ( (α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ) ∘ ((a ▶ φ Γ Δ) ◀ ⊗-context Ξ))
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) )
      ≡⟨ ap (λ z → (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘ (a ▶ φ (Γ ++ Δ) Ξ)
                 ∘ (z ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ)))
            ((◀-▶-comm {f = ⊗-context Ξ} {g = a}) .Isoⁿ.to .is-natural _ _ (φ Γ Δ)) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ (a ▶ φ (Γ ++ Δ) Ξ)
      ∘ ( ((a ▶ (φ Γ Δ ◀ ⊗-context Ξ)) ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ))
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) )
      ≡⟨ ap (λ z → (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘ (a ▶ φ (Γ ++ Δ) Ξ) ∘ z) (sym (assoc _ _ _)) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ (a ▶ φ (Γ ++ Δ) Ξ)
      ∘ ( (a ▶ (φ Γ Δ ◀ ⊗-context Ξ))
        ∘ ( α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
          ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) ) )
      ≡⟨ ap ((a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘_) (assoc _ _ _)
       ∙ assoc _ _ _
       ∙ ap (_∘ ( α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
                ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) ))
            (sym (▶.F-∘ _ _ ∙ ap ((a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘_) (▶.F-∘ _ _))) ⟩
        (a ▶ ⌜ ++-assoc-⊗-iso Γ Δ Ξ .to ∘ φ (Γ ++ Δ) Ξ ∘ (φ Γ Δ ◀ ⊗-context Ξ) ⌝)
      ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
      ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ)
      -- apply the induction hypothesis inside the ▶.
      ≡⟨ ap! (F-α→ Γ Δ Ξ) ⟩
        (a ▶ (φ Γ (Δ ++ Ξ) ∘ (⊗-context Γ ▶ φ Δ Ξ) ∘ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)))
      ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
      ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ)
      -- coh2a: distribute the outer ▶, then pentagon-α→ reassembles the three
      -- associators (φ Γ (Δ++Ξ) and φ Δ Ξ are inert 2-cells; no IH).
      ≡⟨ ap (_∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
                  ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ))
            ( ▶.F-∘ _ _ ∙ ap ((a ▶ φ Γ (Δ ++ Ξ)) ∘_) (▶.F-∘ _ _) ) ⟩
        ((a ▶ φ Γ (Δ ++ Ξ)) ∘ (a ▶ (⊗-context Γ ▶ φ Δ Ξ)) ∘ (a ▶ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)))
      ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
      ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ)
      ≡⟨ sym (assoc _ _ _) ∙ ap ((a ▶ φ Γ (Δ ++ Ξ)) ∘_) (sym (assoc _ _ _)) ⟩
        (a ▶ φ Γ (Δ ++ Ξ))
      ∘ (a ▶ (⊗-context Γ ▶ φ Δ Ξ))
      ∘ ( (a ▶ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ))
        ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) )
      ≡⟨ ap (λ z → (a ▶ φ Γ (Δ ++ Ξ)) ∘ (a ▶ (⊗-context Γ ▶ φ Δ Ξ)) ∘ z) pentagon-α→ ⟩
        (a ▶ φ Γ (Δ ++ Ξ))
      ∘ (a ▶ (⊗-context Γ ▶ φ Δ Ξ))
      ∘ α→ (a , ⊗-context Γ , ⊗-context Δ ⊗ ⊗-context Ξ)
      ∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      -- coh2b: α→ naturality in the third slot pushes φ Δ Ξ outward.
      ≡⟨ ap ((a ▶ φ Γ (Δ ++ Ξ)) ∘_)
            ( assoc _ _ _
            ∙ ap (_∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ))
                 (sym ((▶-assoc {f = a} {g = ⊗-context Γ}) .Isoⁿ.to .is-natural _ _ (φ Δ Ξ)))
            ∙ sym (assoc _ _ _) ) ⟩
        (a ▶ φ Γ (Δ ++ Ξ))
      ∘ α→ (a , ⊗-context Γ , ⊗-context (Δ ++ Ξ))
      ∘ ((a ⊗ ⊗-context Γ) ▶ φ Δ Ξ)
      ∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      -- fold φ (a ∷ Γ) (Δ ++ Ξ) back (definitional, φ-cons) after reassoc.
      ≡⟨ assoc _ _ _
       ∙ ap (_∘ ((a ⊗ ⊗-context Γ) ▶ φ Δ Ξ) ∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ))
            (sym (φ-cons a Γ (Δ ++ Ξ))) ⟩
        φ (a ∷ Γ) (Δ ++ Ξ) ∘ ((a ⊗ ⊗-context Γ) ▶ φ Δ Ξ) ∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      ∎

  -- The .to-direction of the hexagon (ψ = .to everywhere; obtained from F-α→
  -- by inverting every factor).  Used for the assocₘ base plug-assoc-nil [].
  F-α→-to : (Γ Δ Ξ : List Ob)
    →   (⊗-context Γ ▶ (⊗-context-++ Δ Ξ) .to)
      ∘ (⊗-context-++ Γ (Δ ++ Ξ)) .to
      ∘ (++-assoc-⊗-iso Γ Δ Ξ) .to
    ≡   α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      ∘ ((⊗-context-++ Γ Δ) .to ◀ ⊗-context Ξ)
      ∘ (⊗-context-++ (Γ ++ Δ) Ξ) .to
  F-α→-to Γ Δ Ξ = sym helper
    where
      QS : (⊗-context Γ ▶ φ Δ Ξ) ∘ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
         ≡ (⊗-context-++ Γ (Δ ++ Ξ)) .to
             ∘ ( ++-assoc-⊗-iso Γ Δ Ξ .to ∘ (φ (Γ ++ Δ) Ξ ∘ (φ Γ Δ ◀ ⊗-context Ξ)) )
      QS = sym (cancell ((⊗-context-++ Γ (Δ ++ Ξ)) .invl))
         ∙ ap ((⊗-context-++ Γ (Δ ++ Ξ)) .to ∘_) (sym (F-α→ Γ Δ Ξ))

      MID : (⊗-context Γ ▶ φ Δ Ξ)
              ∘ ( α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
                ∘ ( ((⊗-context-++ Γ Δ) .to ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Γ ++ Δ) Ξ) .to ) )
          ≡ (⊗-context-++ Γ (Δ ++ Ξ)) .to ∘ ++-assoc-⊗-iso Γ Δ Ξ .to
      MID =
          assoc _ _ _
        ∙ ap (_∘ (((⊗-context-++ Γ Δ) .to ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Γ ++ Δ) Ξ) .to)) QS
        ∙ sym (assoc _ _ _)
        ∙ ap ((⊗-context-++ Γ (Δ ++ Ξ)) .to ∘_) (sym (assoc _ _ _))
        ∙ ap (λ w → (⊗-context-++ Γ (Δ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Γ Δ Ξ .to ∘ w)) (sym (assoc _ _ _))
        ∙ ap (λ w → (⊗-context-++ Γ (Δ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Γ Δ Ξ .to ∘ (φ (Γ ++ Δ) Ξ ∘ w)))
             (cancell (◀.annihilate ((⊗-context-++ Γ Δ) .invr)))
        ∙ ap (λ w → (⊗-context-++ Γ (Δ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Γ Δ Ξ .to ∘ w))
             ((⊗-context-++ (Γ ++ Δ) Ξ) .invr)
        ∙ ap ((⊗-context-++ Γ (Δ ++ Ξ)) .to ∘_) (idr _)

      helper : α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
                 ∘ ((⊗-context-++ Γ Δ) .to ◀ ⊗-context Ξ)
                 ∘ (⊗-context-++ (Γ ++ Δ) Ξ) .to
             ≡ (⊗-context Γ ▶ (⊗-context-++ Δ Ξ) .to)
                 ∘ (⊗-context-++ Γ (Δ ++ Ξ)) .to
                 ∘ (++-assoc-⊗-iso Γ Δ Ξ) .to
      helper = sym (cancell (▶.annihilate ((⊗-context-++ Δ Ξ) .invl)))
             ∙ ap ((⊗-context Γ ▶ (⊗-context-++ Δ Ξ) .to) ∘_) MID

  Mc : Premulticategory _ _
  Mc .Obₘ = Ob

  Mc .Homₘ Γ τ = Hom (⊗-context Γ) τ

  Mc .Homₘ-set = Hom-set _ _

  Mc .idₘ {x} = ρ← x

  Mc ._∘ₘ_ {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {x = x} f g = f ∘ plug Θ Γ Ξ g

  -- Each law reduces, via the reducing ⊗-context-++ isos, to the corresponding
  -- monoidal coherence: the triangle for the unit laws, the pentagon for
  -- associativity, bifunctoriality for interchange.

  -- Left identity: plugging idₘ = ρ← into x's slot is the identity, since
  -- [x] ++ Ξ = x ∷ Ξ definitionally and the unit that ⊗[x] = x ⊗ Unit
  -- introduces is exactly what ρ← removes (the triangle).
  Mc .idₘl {Θ = Θ} {Ξ = Ξ} {x = x} f =
    ap (f ∘_) plug-ρ ∙ idr f
    where
      split : ⊗-context (Θ ++ x ∷ Ξ) ≅ (⊗-context Θ ⊗ ⊗-context (x ∷ Ξ))
      split = ⊗-context-++ Θ (x ∷ Ξ)
      ψ : ⊗-context (x ∷ Ξ) ≅ (⊗-context (x ∷ []) ⊗ ⊗-context Ξ)
      ψ = ⊗-context-++ (x ∷ []) Ξ

      -- ψ .from = ρ← x ◀ ⊗-context Ξ  (φ.from reduces to the LHS of the
      -- triangle identity triangle-α→).
      φ-from : ψ .from ≡ ρ← x ◀ ⊗-context Ξ
      φ-from = triangle-α→

      -- (apply ρ←) ∘ (insert unit) is the identity: ρ← undoes the unit.
      mid≡id : (⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (ψ .to)) ≡ id
      mid≡id =
          (⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (ψ .to))
        ≡⟨ sym (▶.F-∘ _ _) ⟩
          ⊗-context Θ ▶ (((ρ← x) ◀ ⊗-context Ξ) ∘ ψ .to)
        ≡⟨ ap (⊗-context Θ ▶_) (ap (_∘ ψ .to) (sym φ-from)) ⟩
          ⊗-context Θ ▶ (ψ .from ∘ ψ .to)
        ≡⟨ ap (⊗-context Θ ▶_) (ψ .invr) ⟩
          ⊗-context Θ ▶ id
        ≡⟨ ▶.F-id ⟩
          id
        ∎

      -- plug with g = ρ← is the identity: rebracket (split), apply the
      -- ρ←/unit-cancellation (mid≡id), and rebracket back.
      plug-ρ : plug Θ (x ∷ []) Ξ (ρ← x) ≡ id
      plug-ρ =
          plug Θ (x ∷ []) Ξ (ρ← x)
        ≡⟨⟩
          split .from ∘ (⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ))
            ∘ ((⊗-context Θ ▶ (ψ .to)) ∘ split .to)
        ≡⟨ ap (split .from ∘_) (assoc _ _ _) ⟩
          split .from ∘ (((⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (ψ .to))) ∘ split .to)
        ≡⟨ ap (λ p → split .from ∘ (p ∘ split .to)) mid≡id ⟩
          split .from ∘ (id ∘ split .to)
        ≡⟨ ap (split .from ∘_) (idl _) ⟩
          split .from ∘ split .to
        ≡⟨ split .invr ⟩
          id
        ∎

  Mc .idₘr {Γ = Γ} {z = z} f = to-pathp eq
    where
      -- The three-way split ⊗(Γ++[]) ≅ Unit ⊗ (⊗Γ ⊗ Unit) and the ++-idr iso.
      split : ⊗-context (Γ ++ []) ≅ (Unit ⊗ (⊗-context Γ ⊗ Unit))
      split = ⊗-context-++-++ [] Γ []

      ρ-idr : ⊗-context (Γ ++ []) ≅ ⊗-context Γ
      ρ-idr = ⊗-context-++-idr Γ

      -- intro : ⊗Γ → Unit ⊗ (⊗Γ ⊗ Unit) introduces a unit on each side of ⊗Γ
      -- (the leading [] on the left, the trailing [] on the right).
      intro : Hom (⊗-context Γ) (Unit ⊗ (⊗-context Γ ⊗ Unit))
      intro = split .to ∘ ρ-idr .from

      -- intro = (Unit ▶ ρ→(⊗Γ)) ∘ λ→(⊗Γ): the leading [] contributes λ→ and the
      -- trailing [] contributes ρ→ (via ⊗-context-++-[]-ρ).
      intro-eq : intro ≡ (Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
      intro-eq =
          intro
        ≡⟨⟩
          ((Unit ▶ (⊗-context-++ Γ []) .to) ∘ λ→ _) ∘ ρ-idr .from
        ≡⟨ sym (assoc _ _ _) ⟩
          (Unit ▶ (⊗-context-++ Γ []) .to) ∘ (λ→ _ ∘ ρ-idr .from)
        ≡⟨ ap ((Unit ▶ (⊗-context-++ Γ []) .to) ∘_) (λ→nat (ρ-idr .from)) ⟩
          (Unit ▶ (⊗-context-++ Γ []) .to) ∘ ((Unit ▶ ρ-idr .from) ∘ λ→ (⊗-context Γ))
        ≡⟨ assoc _ _ _ ⟩
          ((Unit ▶ (⊗-context-++ Γ []) .to) ∘ (Unit ▶ ρ-idr .from)) ∘ λ→ (⊗-context Γ)
        ≡⟨ ap (_∘ λ→ (⊗-context Γ)) (sym (▶.F-∘ _ _)) ⟩
          (Unit ▶ ((⊗-context-++ Γ []) .to ∘ ρ-idr .from)) ∘ λ→ (⊗-context Γ)
        ≡⟨ ap (λ p → (Unit ▶ p) ∘ λ→ (⊗-context Γ)) (⊗-context-++-[]-ρ Γ) ⟩
          (Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
        ∎

      -- (Unit ▶ ρ←(⊗Γ)) ∘ intro = λ→(⊗Γ): ρ← undoes the ρ→ that intro-eq inserted.
      sub : (Unit ▶ ρ← (⊗-context Γ)) ∘ intro ≡ λ→ (⊗-context Γ)
      sub =
          (Unit ▶ ρ← (⊗-context Γ)) ∘ intro
        ≡⟨ ap ((Unit ▶ ρ← (⊗-context Γ)) ∘_) intro-eq ⟩
          (Unit ▶ ρ← (⊗-context Γ)) ∘ ((Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ))
        ≡⟨ assoc _ _ _ ⟩
          ((Unit ▶ ρ← (⊗-context Γ)) ∘ (Unit ▶ ρ→ (⊗-context Γ))) ∘ λ→ (⊗-context Γ)
        ≡⟨ ap (_∘ λ→ (⊗-context Γ)) (sym (▶.F-∘ _ _)) ⟩
          (Unit ▶ (ρ← (⊗-context Γ) ∘ ρ→ (⊗-context Γ))) ∘ λ→ (⊗-context Γ)
        ≡⟨ ap (λ p → (Unit ▶ p) ∘ λ→ (⊗-context Γ)) (ρ≅ .invr) ⟩
          (Unit ▶ id) ∘ λ→ (⊗-context Γ)
        ≡⟨ ap (_∘ λ→ (⊗-context Γ)) ▶.F-id ⟩
          id ∘ λ→ (⊗-context Γ)
        ≡⟨ idl _ ⟩
          λ→ (⊗-context Γ)
        ∎

      -- The core equation.  plug [] Γ [] f unfolds to
      --   λ←(z⊗Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ split.to
      -- and split.to ∘ ρ-idr.from = intro, so after regrouping we reduce
      --   ρ←z ∘ λ←(z⊗Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ intro
      -- by the unitor naturality squares (λ←nat, ρ←nat) and the unit
      -- coherences (▶.F-∘, sub, λ≅.invr) to f.
      core : (ρ← z ∘ plug [] Γ [] f) ∘ ρ-idr .from ≡ f
      core =
          (ρ← z ∘ plug [] Γ [] f) ∘ ρ-idr .from
        ≡⟨⟩
          (ρ← z ∘ (λ← (z ⊗ Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ split .to)) ∘ ρ-idr .from
        ≡⟨ sym (assoc _ _ _) ⟩
          ρ← z ∘ ((λ← (z ⊗ Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ split .to) ∘ ρ-idr .from)
        ≡⟨ ap (ρ← z ∘_) (sym (assoc _ _ _)) ⟩
          ρ← z ∘ (λ← (z ⊗ Unit) ∘ ((Unit ▶ (f ◀ Unit)) ∘ split .to) ∘ ρ-idr .from)
        ≡⟨ ap (ρ← z ∘_) (ap (λ← (z ⊗ Unit) ∘_) (sym (assoc _ _ _))) ⟩
          ρ← z ∘ (λ← (z ⊗ Unit) ∘ ((Unit ▶ (f ◀ Unit)) ∘ (split .to ∘ ρ-idr .from)))
        ≡⟨⟩
          ρ← z ∘ (λ← (z ⊗ Unit) ∘ ((Unit ▶ (f ◀ Unit)) ∘ intro))
        ≡⟨ pulll (sym (λ←nat (ρ← z))) ⟩
          (λ← z ∘ (Unit ▶ ρ← z)) ∘ ((Unit ▶ (f ◀ Unit)) ∘ intro)
        ≡⟨ sym (assoc _ _ _) ⟩
          λ← z ∘ ((Unit ▶ ρ← z) ∘ ((Unit ▶ (f ◀ Unit)) ∘ intro))
        ≡⟨ ap (λ← z ∘_) (pulll (sym (▶.F-∘ _ _))) ⟩
          λ← z ∘ ((Unit ▶ (ρ← z ∘ (f ◀ Unit))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (ap (_∘ intro) (ap (Unit ▶_) (ρ←nat f))) ⟩
          λ← z ∘ ((Unit ▶ (f ∘ ρ← (⊗-context Γ))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (ap (_∘ intro) (▶.F-∘ _ _)) ⟩
          λ← z ∘ (((Unit ▶ f) ∘ (Unit ▶ ρ← (⊗-context Γ))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (sym (assoc _ _ _)) ⟩
          λ← z ∘ ((Unit ▶ f) ∘ ((Unit ▶ ρ← (⊗-context Γ)) ∘ intro))
        ≡⟨ ap (λ← z ∘_) (ap ((Unit ▶ f) ∘_) sub) ⟩
          λ← z ∘ ((Unit ▶ f) ∘ λ→ (⊗-context Γ))
        ≡⟨ pulll (λ←nat f) ⟩
          (f ∘ λ← (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
        ≡⟨ sym (assoc _ _ _) ⟩
          f ∘ (λ← (⊗-context Γ) ∘ λ→ (⊗-context Γ))
        ≡⟨ ap (f ∘_) (λ≅ .invr) ⟩
          f ∘ id
        ≡⟨ idr _ ⟩
          f
        ∎

      eq : transport (λ i → Hom (⊗-context (++-idr Γ i)) z) (ρ← z ∘ plug [] Γ [] f) ≡ f
      eq =
          transport (λ i → Hom (⊗-context (++-idr Γ i)) z) (ρ← z ∘ plug [] Γ [] f)
        ≡⟨ subst-⊗-red (++-idr Γ) (⊗-context-++-idr-path Γ) (ρ← z ∘ plug [] Γ [] f) ⟩
          (ρ← z ∘ plug [] Γ [] f) ∘ (⊗-context-++-idr Γ) .from
        ≡⟨ core ⟩
          f
        ∎
  Mc .assocₘ {Θ = Θ} {Ξ = Ξ} {Φ = Φ} {Ψ = Ψ} {Ρ = Ρ} {x = x} {y = y} {z = z} f g h = to-pathp eq
    where
      slot-iso : ⊗-context (Θ ++ ((Φ ++ y ∷ Ψ) ++ Ξ)) ≅ ⊗-context ((Θ ++ Φ) ++ y ∷ (Ψ ++ Ξ))
      slot-iso = slot-unbury-iso Θ Φ y Ψ Ξ

      bdry-iso : ⊗-context ((Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ)) ≅ ⊗-context (Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ))
      bdry-iso = assocₘ-boundary-iso Θ Φ Ρ Ψ Ξ

      plugL = plug Θ (Φ ++ y ∷ Ψ) Ξ g
      plugH = plug (Θ ++ Φ) Ρ (Ψ ++ Ξ) h
      plugGH = plug Φ Ρ Ψ h
      plugR = plug Θ (Φ ++ Ρ ++ Ψ) Ξ (g ∘ plugGH)

      subst-red : subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL)
                  ≡ (f ∘ plugL) ∘ slot-iso .from
      subst-red = subst-⊗-red (slot-unbury Θ Φ y Ψ Ξ) (slot-unbury-⊗ Θ Φ y Ψ Ξ) (f ∘ plugL)

      -- The f-free plug coherence (the pentagon): plugging h into the relocated
      -- slot of (f∘ₘg) equals plugging (g∘ₘh) into f's slot.  f is cancelled by
      -- `ap (f ∘_)`; this is the residual that remains after transport reduction.
      -- Aliases for the plug's split/decompose isos (see `plug` definition):
      --   plug Θ Γ Ξ k = splitL.from ∘ (⊗Θ ▶ (k ◀ ⊗Ξ)) ∘ dec.to
      splitL = ⊗-context-++ Θ (x ∷ Ξ)
      decL   = ⊗-context-++-++ Θ (Φ ++ y ∷ Ψ) Ξ
      decR   = ⊗-context-++-++ Θ (Φ ++ Ρ ++ Ψ) Ξ

      -- The Θ=[] core, generalised over Φ so it can recurse: the 2-way-split
      -- version of plug-assoc (⊗-context-++/++-assoc-⊗/assocₘ-flatten in place of the
      -- -++-++/slot-unbury/assocₘ-boundary isos).  Cons on Φ mirrors plug-assoc's cons
      -- (pp-cons is refl, so the ⊗-context-++ split unfolds definitionally);
      -- the RHS plug also carries a prefix, pushed out with ◀-▶-comm.
      plug-assoc-nil : (Φ' : List Ob)
        → (⊗-context-++ (Φ' ++ y ∷ Ψ) Ξ) .to
            ∘ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from
            ∘ plug Φ' Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from
          ≡ (plug Φ' Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Φ' ++ Ρ ++ Ψ) Ξ) .to
      plug-assoc-nil [] =
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ (++-assoc-⊗-iso [] (y ∷ Ψ) Ξ) .from
            ∘ ⌜ plug [] Ρ (Ψ ++ Ξ) h ⌝
            ∘ (assocₘ-flatten-iso [] Ρ Ψ Ξ) .from
        ≡⟨ ap! (plug-nil Ρ (Ψ ++ Ξ) h) ⟩
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ (++-assoc-⊗-iso [] (y ∷ Ψ) Ξ) .from
            ∘ ((h ◀ ⊗-context (Ψ ++ Ξ)) ∘ (⊗-context-++ Ρ (Ψ ++ Ξ)) .to)
            ∘ ⌜ (assocₘ-flatten-iso [] Ρ Ψ Ξ) .from ⌝
        ≡⟨ ap! (flat-from Ρ Ψ Ξ) ⟩
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ (++-assoc-⊗-iso [] (y ∷ Ψ) Ξ) .from
            ∘ ((h ◀ ⊗-context (Ψ ++ Ξ)) ∘ (⊗-context-++ Ρ (Ψ ++ Ξ)) .to)
            ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to
        ≡⟨ ap ((⊗-context-++ (y ∷ Ψ) Ξ) .to ∘_) (idl _) ⟩
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ ( ((h ◀ ⊗-context (Ψ ++ Ξ)) ∘ (⊗-context-++ Ρ (Ψ ++ Ξ)) .to)
              ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to )
        -- unfold ψ(y∷Ψ) = α← ∘ (y ▶ ψ Ψ Ξ) (pp-cons, definitional), pull α← out.
        ≡⟨ sym (assoc _ _ _)
         ∙ ap (α← (y , ⊗-context Ψ , ⊗-context Ξ) ∘_)
              (ap ((y ▶ (⊗-context-++ Ψ Ξ) .to) ∘_) (sym (assoc _ _ _))) ⟩
          α← (y , ⊗-context Ψ , ⊗-context Ξ)
            ∘ ( (y ▶ (⊗-context-++ Ψ Ξ) .to)
              ∘ ( (h ◀ ⊗-context (Ψ ++ Ξ))
                ∘ ((⊗-context-++ Ρ (Ψ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to) ) )
        -- bifunctor interchange: slide h past y ▶ ψΨΞ.
        ≡⟨ ap (α← (y , ⊗-context Ψ , ⊗-context Ξ) ∘_) (extendl (-⊗-.rlmap _ _)) ⟩
          α← (y , ⊗-context Ψ , ⊗-context Ξ)
            ∘ ( (h ◀ (⊗-context Ψ ⊗ ⊗-context Ξ))
              ∘ ( (⊗-context Ρ ▶ (⊗-context-++ Ψ Ξ) .to)
                ∘ ((⊗-context-++ Ρ (Ψ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to) ) )
        -- the h-free tail is the .to-hexagon F-α→-to Ρ Ψ Ξ.
        ≡⟨ ap (λ w → α← (y , ⊗-context Ψ , ⊗-context Ξ) ∘ ((h ◀ (⊗-context Ψ ⊗ ⊗-context Ξ)) ∘ w))
              (F-α→-to Ρ Ψ Ξ) ⟩
          α← (y , ⊗-context Ψ , ⊗-context Ξ)
            ∘ ( (h ◀ (⊗-context Ψ ⊗ ⊗-context Ξ))
              ∘ ( α→ (⊗-context Ρ , ⊗-context Ψ , ⊗-context Ξ)
                ∘ ( ((⊗-context-++ Ρ Ψ) .to ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to ) ) )
        -- α→ naturality in the first slot (h): pull h out to (h◀⊗Ψ)◀⊗Ξ.
        ≡⟨ ap (α← (y , ⊗-context Ψ , ⊗-context Ξ) ∘_)
              (extendl (sym ((◀-assoc {f = ⊗-context Ψ} {g = ⊗-context Ξ}) .Isoⁿ.from .is-natural _ _ h))) ⟩
          α← (y , ⊗-context Ψ , ⊗-context Ξ)
            ∘ ( α→ (y , ⊗-context Ψ , ⊗-context Ξ)
              ∘ ( ((h ◀ ⊗-context Ψ) ◀ ⊗-context Ξ)
                ∘ ( ((⊗-context-++ Ρ Ψ) .to ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to ) ) )
        -- α← ∘ α→ = id.
        ≡⟨ cancell (α≅ .invr) ⟩
          ((h ◀ ⊗-context Ψ) ◀ ⊗-context Ξ)
            ∘ ( ((⊗-context-++ Ρ Ψ) .to ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to )
        -- fold ◀ and plug-nil to reach the RHS.
        ≡⟨ assoc _ _ _
         ∙ ap (_∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to) (sym (◀.F-∘ _ _))
         ∙ ap (λ w → (w ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to) (sym (plug-nil Ρ Ψ h)) ⟩
          (plug [] Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Ρ ++ Ψ) Ξ) .to
        ∎
      plug-assoc-nil (b ∷ Φ') =
          (⊗-context-++ ((b ∷ Φ') ++ y ∷ Ψ) Ξ) .to
            ∘ (b ▶ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from)
            ∘ plug (b ∷ Φ') Ρ (Ψ ++ Ξ) h
            ∘ (b ▶ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from)
        ≡⟨ ap (λ z → (⊗-context-++ ((b ∷ Φ') ++ y ∷ Ψ) Ξ) .to
                   ∘ (b ▶ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from)
                   ∘ z
                   ∘ (b ▶ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from))
              (plug-cons b Φ' Ρ (Ψ ++ Ξ) h) ⟩
          (α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ)
            ∘ (b ▶ (⊗-context-++ (Φ' ++ y ∷ Ψ) Ξ) .to))
            ∘ (b ▶ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from)
            ∘ (b ▶ plug Φ' Ρ (Ψ ++ Ξ) h)
            ∘ (b ▶ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from)
        ≡⟨ sym (assoc _ _ _)
         ∙ ap (α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ) ∘_)
              (sym ( ▶.F-∘ _ _
                   ∙ ap ((b ▶ (⊗-context-++ (Φ' ++ y ∷ Ψ) Ξ) .to) ∘_)
                        (▶.F-∘ _ _ ∙ ap ((b ▶ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from) ∘_) (▶.F-∘ _ _)) )) ⟩
          α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ)
            ∘ (b ▶ ⌜ (⊗-context-++ (Φ' ++ y ∷ Ψ) Ξ) .to
                   ∘ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from
                   ∘ plug Φ' Ρ (Ψ ++ Ξ) h
                   ∘ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from ⌝)
        ≡⟨ ap! (plug-assoc-nil Φ') ⟩
          α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ)
            ∘ (b ▶ ((plug Φ' Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Φ' ++ Ρ ++ Ψ) Ξ) .to))
        ≡⟨ ap (α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ) ∘_) (▶.F-∘ _ _) ⟩
          α← (b , ⊗-context (Φ' ++ y ∷ Ψ) , ⊗-context Ξ)
            ∘ ( (b ▶ (plug Φ' Ρ Ψ h ◀ ⊗-context Ξ))
              ∘ (b ▶ (⊗-context-++ (Φ' ++ Ρ ++ Ψ) Ξ) .to) )
        ≡⟨ extendl ((◀-▶-comm {f = ⊗-context Ξ} {g = b}) .Isoⁿ.from .is-natural _ _ (plug Φ' Ρ Ψ h)) ⟩
          ((b ▶ plug Φ' Ρ Ψ h) ◀ ⊗-context Ξ)
            ∘ ( α← (b , ⊗-context (Φ' ++ Ρ ++ Ψ) , ⊗-context Ξ)
              ∘ (b ▶ (⊗-context-++ (Φ' ++ Ρ ++ Ψ) Ξ) .to) )
        ≡⟨ ap (λ z → (z ◀ ⊗-context Ξ)
                   ∘ ( α← (b , ⊗-context (Φ' ++ Ρ ++ Ψ) , ⊗-context Ξ)
                     ∘ (b ▶ (⊗-context-++ (Φ' ++ Ρ ++ Ψ) Ξ) .to) ))
              (sym (plug-cons b Φ' Ρ Ψ h)) ⟩
          (plug (b ∷ Φ') Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ ((b ∷ Φ') ++ Ρ ++ Ψ) Ξ) .to
        ∎

      -- g cancelled: decL.to ∘ slot-iso.from ∘ plugH ∘ bdry-iso.from
      --              = (⊗Θ ▶ (plugGH ◀ ⊗Ξ)) ∘ decR.to   (only h remains).
      -- Proved by induction on the prefix Θ: the slot/boundary isos are clean
      -- ▶-recursions, and dec/plug carry α→ corrections (as in F-α→'s cons).
      plug-assoc : (Θ' : List Ob)
        → (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to
            ∘ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from
            ∘ plug (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from
          ≡ (⊗-context Θ' ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ (⊗-context-++-++ Θ' (Φ ++ Ρ ++ Ψ) Ξ) .to
      -- Base: no outer prefix.  Reduces (via λ→ naturality on the ⊗-context-++-++ []
      -- = λ→ ∘ ⊗-context-++ unfolding, see split3-nil) to the Φ-indexed coherence
      -- plug-assoc-nil (same statement with ⊗-context-++ / ++-assoc-⊗ / assocₘ-flatten in
      -- place of the -++-++ / slot-unbury / assocₘ-boundary isos), provable by a
      -- further induction on Φ (cons: pp-cons refl + plug-cons + ▶-assoc, exactly
      -- like the Θ-cons above; base Φ=[] bottoms out in a Ρ-induction from
      -- assocₘ-flatten with a unit/triangle core).
      plug-assoc [] =
          (⊗-context-++-++ [] (Φ ++ y ∷ Ψ) Ξ) .to
            ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
            ∘ plug Φ Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from
        ≡⟨ ap (λ z → z ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
                   ∘ plug Φ Ρ (Ψ ++ Ξ) h
                   ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from)
              (split3-nil (Φ ++ y ∷ Ψ) Ξ) ⟩
          (λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ y ∷ Ψ) Ξ) .to)
            ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
            ∘ plug Φ Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from
        ≡⟨ sym (assoc _ _ _) ⟩
          λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ ( (⊗-context-++ (Φ ++ y ∷ Ψ) Ξ) .to
              ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
              ∘ plug Φ Ρ (Ψ ++ Ξ) h
              ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from )
        ≡⟨ ap (λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘_) (plug-assoc-nil Φ) ⟩
          λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ ((plug Φ Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to)
        ≡⟨ assoc _ _ _ ⟩
          (λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘ (plug Φ Ρ Ψ h ◀ ⊗-context Ξ))
            ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to
        ≡⟨ ap (_∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to)
              (λ→nat (plugGH ◀ ⊗-context Ξ)) ⟩
          ((Unit ▶ (plugGH ◀ ⊗-context Ξ)) ∘ λ→ (⊗-context (Φ ++ Ρ ++ Ψ) ⊗ ⊗-context Ξ))
            ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to
        ≡⟨ sym (assoc _ _ _) ⟩
          (Unit ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ (λ→ (⊗-context (Φ ++ Ρ ++ Ψ) ⊗ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to)
        ≡⟨ ap ((Unit ▶ (plugGH ◀ ⊗-context Ξ)) ∘_) (sym (split3-nil (Φ ++ Ρ ++ Ψ) Ξ)) ⟩
          (⊗-context [] ▶ (plugGH ◀ ⊗-context Ξ)) ∘ (⊗-context-++-++ [] (Φ ++ Ρ ++ Ψ) Ξ) .to
        ∎
      plug-assoc (a ∷ Θ') =
          (⊗-context-++-++ (a ∷ Θ') (Φ ++ y ∷ Ψ) Ξ) .to
            ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
            ∘ plug ((a ∷ Θ') ++ Φ) Ρ (Ψ ++ Ξ) h
            ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from)
        ≡⟨ ap (λ z → z ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
                   ∘ plug ((a ∷ Θ') ++ Φ) Ρ (Ψ ++ Ξ) h
                   ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from))
              (split3-cons a Θ' (Φ ++ y ∷ Ψ) Ξ) ⟩
          (α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ (a ▶ (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to))
            ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
            ∘ plug ((a ∷ Θ') ++ Φ) Ρ (Ψ ++ Ξ) h
            ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from)
        ≡⟨ ap (λ z → (α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
                        ∘ (a ▶ (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to))
                     ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
                     ∘ z
                     ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from))
              (plug-cons a (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h) ⟩
          (α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ (a ▶ (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to))
            ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
            ∘ (a ▶ plug (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h)
            ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from)
        ≡⟨ sym (assoc _ _ _)
         ∙ ap (α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘_)
              (sym ( ▶.F-∘ _ _
                   ∙ ap ((a ▶ (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to) ∘_)
                        (▶.F-∘ _ _ ∙ ap ((a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from) ∘_) (▶.F-∘ _ _)) )) ⟩
          α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ (a ▶ ⌜ (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to
                   ∘ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from
                   ∘ plug (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h
                   ∘ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from ⌝)
        ≡⟨ ap! (plug-assoc Θ') ⟩
          α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ (a ▶ ( (⊗-context Θ' ▶ (plugGH ◀ ⊗-context Ξ))
                   ∘ (⊗-context-++-++ Θ' (Φ ++ Ρ ++ Ψ) Ξ) .to ))
        ≡⟨ ap (α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘_) (▶.F-∘ _ _) ⟩
          α← (a , ⊗-context Θ' , ⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ ( (a ▶ (⊗-context Θ' ▶ (plugGH ◀ ⊗-context Ξ)))
              ∘ (a ▶ (⊗-context-++-++ Θ' (Φ ++ Ρ ++ Ψ) Ξ) .to) )
        ≡⟨ extendl ((▶-assoc {f = a} {g = ⊗-context Θ'}) .Isoⁿ.from .is-natural _ _ (plugGH ◀ ⊗-context Ξ)) ⟩
          ((a ⊗ ⊗-context Θ') ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ ( α← (a , ⊗-context Θ' , ⊗-context (Φ ++ Ρ ++ Ψ) ⊗ ⊗-context Ξ)
              ∘ (a ▶ (⊗-context-++-++ Θ' (Φ ++ Ρ ++ Ψ) Ξ) .to) )
        ≡⟨ ap (((a ⊗ ⊗-context Θ') ▶ (plugGH ◀ ⊗-context Ξ)) ∘_)
              (sym (split3-cons a Θ' (Φ ++ Ρ ++ Ψ) Ξ)) ⟩
          (⊗-context (a ∷ Θ') ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ (⊗-context-++-++ (a ∷ Θ') (Φ ++ Ρ ++ Ψ) Ξ) .to
        ∎

      g-free : decL .to ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from
               ≡ (⊗-context Θ ▶ (plugGH ◀ ⊗-context Ξ)) ∘ decR .to
      g-free = plug-assoc Θ

      plug-coherence : plugL ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from ≡ plugR
      plug-coherence =
          plugL ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from
        ≡⟨⟩
          (splitL .from ∘ (⊗-context Θ ▶ (g ◀ ⊗-context Ξ)) ∘ decL .to)
            ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from
        ≡⟨ sym (assoc _ _ _) ⟩
          splitL .from
            ∘ (((⊗-context Θ ▶ (g ◀ ⊗-context Ξ)) ∘ decL .to)
               ∘ (slot-iso .from ∘ plugH ∘ bdry-iso .from))
        ≡⟨ ap (splitL .from ∘_) (sym (assoc _ _ _)) ⟩
          splitL .from
            ∘ ((⊗-context Θ ▶ (g ◀ ⊗-context Ξ))
               ∘ (decL .to ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from))
        ≡⟨ ap (λ ξ → splitL .from ∘ ((⊗-context Θ ▶ (g ◀ ⊗-context Ξ)) ∘ ξ)) g-free ⟩
          splitL .from
            ∘ ((⊗-context Θ ▶ (g ◀ ⊗-context Ξ))
               ∘ ((⊗-context Θ ▶ (plugGH ◀ ⊗-context Ξ)) ∘ decR .to))
        ≡⟨ ap (splitL .from ∘_) (assoc _ _ _ ∙ ap (_∘ decR .to) (▶.collapse (sym (◀.F-∘ g plugGH)))) ⟩
          splitL .from ∘ ((⊗-context Θ ▶ ((g ∘ plugGH) ◀ ⊗-context Ξ)) ∘ decR .to)
        ≡⟨⟩
          plugR
        ∎

      eq : transport (λ i → Hom (⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ i)) z)
              (subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL) ∘ plugH)
            ≡ (f ∘ plugR)
      eq =
          transport (λ i → Hom (⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ i)) z)
            (subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL) ∘ plugH)
        ≡⟨ ap (λ ◆ → transport (λ i → Hom (⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ i)) z) (◆ ∘ plugH))
              subst-red ⟩
          transport (λ i → Hom (⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ i)) z)
            (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH)
        ≡⟨ subst-⊗-red (assocₘ-boundary Θ Φ Ρ Ψ Ξ) (assocₘ-boundary-⊗ Θ Φ Ρ Ψ Ξ)
              (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH) ⟩
          (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH) ∘ bdry-iso .from
        ≡⟨ sym (assoc _ _ _) ⟩
          ((f ∘ plugL) ∘ slot-iso .from) ∘ (plugH ∘ bdry-iso .from)
        ≡⟨ sym (assoc _ _ _) ⟩
          (f ∘ plugL) ∘ (slot-iso .from ∘ (plugH ∘ bdry-iso .from))
        ≡⟨ sym (assoc _ _ _) ⟩
          f ∘ (plugL ∘ (slot-iso .from ∘ (plugH ∘ bdry-iso .from)))
        ≡⟨ ap (f ∘_) plug-coherence ⟩
          f ∘ plugR
        ∎
  Mc .interchangeₘ {Θ = Θ} {Μ = Μ} {Κ = Κ} {Γ = Γ} {Δ = Δ} {x = x} {y = y} {z = z} f g h = to-pathp eq
    where
      -- f's two slots are x (at Θ++x∷Μ) and y (at Μ++y∷Κ).  Plugs:
      plugg   = plug Θ Γ (Μ ++ y ∷ Κ) g            -- g into x's slot
      plugg₂  = plug Θ Γ (Μ ++ Δ ++ Κ) g           -- g into x's slot (after h)
      plugh₁  = plug (Θ ++ Γ ++ Μ) Δ Κ h           -- h into y's slot (after g)
      plugh₂  = plug (Θ ++ x ∷ Μ) Δ Κ h            -- h into y's slot

      slot₀-iso = ic-slot₀-iso Θ x Μ y Κ
      slot₁-iso = ic-slot₁-iso Θ Γ Μ y Κ
      slot₂-iso = ic-slot₂-iso Θ x Μ Δ Κ
      bdry-iso  = ic-boundary-iso Θ Γ Μ Δ Κ

      subst₀ : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f
               ≡ f ∘ slot₀-iso .from
      subst₀ = subst-⊗-red (interchange-slot₀ Θ x Μ y Κ) (ic-slot₀-⊗ Θ x Μ y Κ) f

      subst₁ : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg)
               ≡ (f ∘ plugg) ∘ slot₁-iso .from
      subst₁ = subst-⊗-red (interchange-slot₁ Θ Γ Μ y Κ) (ic-slot₁-⊗ Θ Γ Μ y Κ) (f ∘ plugg)

      subst₂-red : (M : Hom (⊗-context ((Θ ++ x ∷ Μ) ++ Δ ++ Κ)) z)
        → subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ) M ≡ M ∘ slot₂-iso .from
      subst₂-red = subst-⊗-red (interchange-slot₂ Θ x Μ Δ Κ) (ic-slot₂-⊗ Θ x Μ Δ Κ)

      -- The g-free remainder of the interchange base (Θ=[]), generalised over Γ
      -- so it can recurse: relates plug (Γ++Μ) h to (⊗Γ ▶ plug Μ h).  Since g has
      -- been factored out, Γ-induction is legitimate (h, plug Μ h are Γ-fixed).
      -- Cons mirrors plug-assoc's cons (pp-cons refl + plug-cons + ▶-assoc push-out);
      -- base Γ=[] is left-unitor naturality.
      plug-shift : (Γ' : List Ob)
        →   (⊗-context-++ Γ' (Μ ++ y ∷ Κ)) .to
              ∘ (ic-slot₁-iso [] Γ' Μ y Κ) .from
              ∘ plug (Γ' ++ Μ) Δ Κ h
              ∘ (ic-flatten-iso Γ' Μ Δ Κ) .from
          ≡   (⊗-context Γ' ▶ plug Μ Δ Κ h)
              ∘ (⊗-context-++ Γ' (Μ ++ Δ ++ Κ)) .to
      plug-shift [] =
          ap (λ→ (⊗-context (Μ ++ y ∷ Κ)) ∘_) (idl _ ∙ idr _)
        ∙ λ→nat (plug Μ Δ Κ h)
      plug-shift (b ∷ Γ') =
          (⊗-context-++ (b ∷ Γ') (Μ ++ y ∷ Κ)) .to
            ∘ (b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from)
            ∘ plug ((b ∷ Γ') ++ Μ) Δ Κ h
            ∘ (b ▶ (ic-flatten-iso Γ' Μ Δ Κ) .from)
        ≡⟨ ap (λ w → (⊗-context-++ (b ∷ Γ') (Μ ++ y ∷ Κ)) .to ∘ (b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from)
                   ∘ w ∘ (b ▶ (ic-flatten-iso Γ' Μ Δ Κ) .from))
              (plug-cons b (Γ' ++ Μ) Δ Κ h) ⟩
          (α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ)) ∘ (b ▶ (⊗-context-++ Γ' (Μ ++ y ∷ Κ)) .to))
            ∘ (b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from)
            ∘ (b ▶ plug (Γ' ++ Μ) Δ Κ h)
            ∘ (b ▶ (ic-flatten-iso Γ' Μ Δ Κ) .from)
        ≡⟨ sym (assoc _ _ _)
         ∙ ap (α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ)) ∘_)
              (sym ( ▶.F-∘ _ _
                   ∙ ap ((b ▶ (⊗-context-++ Γ' (Μ ++ y ∷ Κ)) .to) ∘_)
                        (▶.F-∘ _ _ ∙ ap ((b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from) ∘_) (▶.F-∘ _ _)) )) ⟩
          α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ))
            ∘ (b ▶ ⌜ (⊗-context-++ Γ' (Μ ++ y ∷ Κ)) .to
                   ∘ (ic-slot₁-iso [] Γ' Μ y Κ) .from
                   ∘ plug (Γ' ++ Μ) Δ Κ h
                   ∘ (ic-flatten-iso Γ' Μ Δ Κ) .from ⌝)
        ≡⟨ ap! (plug-shift Γ') ⟩
          α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ))
            ∘ (b ▶ ((⊗-context Γ' ▶ plug Μ Δ Κ h) ∘ (⊗-context-++ Γ' (Μ ++ Δ ++ Κ)) .to))
        ≡⟨ ap (α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ)) ∘_) (▶.F-∘ _ _) ⟩
          α← (b , ⊗-context Γ' , ⊗-context (Μ ++ y ∷ Κ))
            ∘ ( (b ▶ (⊗-context Γ' ▶ plug Μ Δ Κ h)) ∘ (b ▶ (⊗-context-++ Γ' (Μ ++ Δ ++ Κ)) .to) )
        ≡⟨ extendl ((▶-assoc {f = b} {g = ⊗-context Γ'}) .Isoⁿ.from .is-natural _ _ (plug Μ Δ Κ h)) ⟩
          (⊗-context (b ∷ Γ') ▶ plug Μ Δ Κ h) ∘ (⊗-context-++ (b ∷ Γ') (Μ ++ Δ ++ Κ)) .to
        ∎

      -- the f-free bifunctoriality coherence (the hard piece), by induction on
      -- the prefix Θ.  Cons is clean: every factor is a ▶ (plug is prefix-linear
      -- via plug-cons; the ic-slot isos are ▶.F-map-iso), so no α corrections.
      plug-interchange : (Θ' : List Ob)
        →   plug Θ' Γ (Μ ++ y ∷ Κ) g
              ∘ (ic-slot₁-iso Θ' Γ Μ y Κ) .from
              ∘ plug (Θ' ++ Γ ++ Μ) Δ Κ h
              ∘ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from
          ≡   (ic-slot₀-iso Θ' x Μ y Κ) .from
              ∘ plug (Θ' ++ x ∷ Μ) Δ Κ h
              ∘ (ic-slot₂-iso Θ' x Μ Δ Κ) .from
              ∘ plug Θ' Γ (Μ ++ Δ ++ Κ) g
      plug-interchange [] =
          plug [] Γ (Μ ++ y ∷ Κ) g
            ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
            ∘ plug ([] ++ Γ ++ Μ) Δ Κ h
            ∘ (ic-boundary-iso [] Γ Μ Δ Κ) .from
        ≡⟨ ap (λ w → w ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
                   ∘ plug ([] ++ Γ ++ Μ) Δ Κ h ∘ (ic-boundary-iso [] Γ Μ Δ Κ) .from)
              (plug-nil Γ (Μ ++ y ∷ Κ) g) ⟩
          ((g ◀ ⊗-context (Μ ++ y ∷ Κ)) ∘ (⊗-context-++ Γ (Μ ++ y ∷ Κ)) .to)
            ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
            ∘ plug (Γ ++ Μ) Δ Κ h
            ∘ (ic-flatten-iso Γ Μ Δ Κ) .from
        ≡⟨ sym (assoc _ _ _) ⟩
          (g ◀ ⊗-context (Μ ++ y ∷ Κ))
            ∘ ( (⊗-context-++ Γ (Μ ++ y ∷ Κ)) .to
              ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
              ∘ plug (Γ ++ Μ) Δ Κ h
              ∘ (ic-flatten-iso Γ Μ Δ Κ) .from )
        ≡⟨ ap ((g ◀ ⊗-context (Μ ++ y ∷ Κ)) ∘_) (plug-shift Γ) ⟩
          (g ◀ ⊗-context (Μ ++ y ∷ Κ))
            ∘ ((⊗-context Γ ▶ plug Μ Δ Κ h) ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to)
        ≡⟨ assoc _ _ _ ⟩
          ((g ◀ ⊗-context (Μ ++ y ∷ Κ)) ∘ (⊗-context Γ ▶ plug Μ Δ Κ h))
            ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to
        ≡⟨ ap (_∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to)
              (sym (-⊗-.rlmap (plug Μ Δ Κ h) g)) ⟩
          ((x ▶ plug Μ Δ Κ h) ∘ (g ◀ ⊗-context (Μ ++ Δ ++ Κ)))
            ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to
        ≡⟨ sym (assoc _ _ _) ⟩
          (x ▶ plug Μ Δ Κ h)
            ∘ ((g ◀ ⊗-context (Μ ++ Δ ++ Κ)) ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to)
        ≡⟨ ap ((x ▶ plug Μ Δ Κ h) ∘_) (sym (plug-nil Γ (Μ ++ Δ ++ Κ) g)) ⟩
          (x ▶ plug Μ Δ Κ h) ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ≡⟨ ap (_∘ plug [] Γ (Μ ++ Δ ++ Κ) g) (sym (plug-cons x Μ Δ Κ h)) ⟩
          plug (x ∷ Μ) Δ Κ h ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ≡⟨ ap (plug (x ∷ Μ) Δ Κ h ∘_) (sym (idl _)) ∙ sym (idl _) ⟩
          (ic-slot₀-iso [] x Μ y Κ) .from
            ∘ plug (x ∷ Μ) Δ Κ h
            ∘ (ic-slot₂-iso [] x Μ Δ Κ) .from
            ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ∎
      plug-interchange (a ∷ Θ') =
          plug (a ∷ Θ') Γ (Μ ++ y ∷ Κ) g
            ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
            ∘ plug ((a ∷ Θ') ++ Γ ++ Μ) Δ Κ h
            ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from)
        ≡⟨ ap (λ w → w ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
                   ∘ plug ((a ∷ Θ') ++ Γ ++ Μ) Δ Κ h ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from))
              (plug-cons a Θ' Γ (Μ ++ y ∷ Κ) g) ⟩
          (a ▶ plug Θ' Γ (Μ ++ y ∷ Κ) g)
            ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
            ∘ plug ((a ∷ Θ') ++ Γ ++ Μ) Δ Κ h
            ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from)
        ≡⟨ ap (λ w → (a ▶ plug Θ' Γ (Μ ++ y ∷ Κ) g) ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
                   ∘ w ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from))
              (plug-cons a (Θ' ++ Γ ++ Μ) Δ Κ h) ⟩
          (a ▶ plug Θ' Γ (Μ ++ y ∷ Κ) g)
            ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
            ∘ (a ▶ plug (Θ' ++ Γ ++ Μ) Δ Κ h)
            ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from)
        ≡⟨ sym ( ▶.F-∘ _ _
               ∙ ap ((a ▶ plug Θ' Γ (Μ ++ y ∷ Κ) g) ∘_)
                    (▶.F-∘ _ _ ∙ ap ((a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from) ∘_) (▶.F-∘ _ _)) ) ⟩
          a ▶ ( plug Θ' Γ (Μ ++ y ∷ Κ) g
              ∘ (ic-slot₁-iso Θ' Γ Μ y Κ) .from
              ∘ plug (Θ' ++ Γ ++ Μ) Δ Κ h
              ∘ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from )
        ≡⟨ ap (a ▶_) (plug-interchange Θ') ⟩
          a ▶ ( (ic-slot₀-iso Θ' x Μ y Κ) .from
              ∘ plug (Θ' ++ x ∷ Μ) Δ Κ h
              ∘ (ic-slot₂-iso Θ' x Μ Δ Κ) .from
              ∘ plug Θ' Γ (Μ ++ Δ ++ Κ) g )
        ≡⟨ ▶.F-∘ _ _
         ∙ ap ((a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from) ∘_)
              (▶.F-∘ _ _ ∙ ap ((a ▶ plug (Θ' ++ x ∷ Μ) Δ Κ h) ∘_) (▶.F-∘ _ _)) ⟩
          (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
            ∘ (a ▶ plug (Θ' ++ x ∷ Μ) Δ Κ h)
            ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from)
            ∘ (a ▶ plug Θ' Γ (Μ ++ Δ ++ Κ) g)
        ≡⟨ ap (λ w → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from) ∘ w
                   ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from) ∘ (a ▶ plug Θ' Γ (Μ ++ Δ ++ Κ) g))
              (sym (plug-cons a (Θ' ++ x ∷ Μ) Δ Κ h)) ⟩
          (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
            ∘ plug ((a ∷ Θ') ++ x ∷ Μ) Δ Κ h
            ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from)
            ∘ (a ▶ plug Θ' Γ (Μ ++ Δ ++ Κ) g)
        ≡⟨ ap (λ w → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from) ∘ plug ((a ∷ Θ') ++ x ∷ Μ) Δ Κ h
                   ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from) ∘ w)
              (sym (plug-cons a Θ' Γ (Μ ++ Δ ++ Κ) g)) ⟩
          (ic-slot₀-iso (a ∷ Θ') x Μ y Κ) .from
            ∘ plug ((a ∷ Θ') ++ x ∷ Μ) Δ Κ h
            ∘ (ic-slot₂-iso (a ∷ Θ') x Μ Δ Κ) .from
            ∘ plug (a ∷ Θ') Γ (Μ ++ Δ ++ Κ) g
        ∎

      ic-plug-coherence
        :   plugg ∘ slot₁-iso .from ∘ plugh₁ ∘ bdry-iso .from
        ≡ slot₀-iso .from ∘ plugh₂ ∘ slot₂-iso .from ∘ plugg₂
      ic-plug-coherence = plug-interchange Θ

      rest₂ = slot₀-iso .from ∘ (plugh₂ ∘ (slot₂-iso .from ∘ plugg₂))

      RHS-red : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ)
                  (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f ∘ plugh₂) ∘ plugg₂
                ≡ f ∘ rest₂
      RHS-red =
          ap (λ ◆ → subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ) (◆ ∘ plugh₂) ∘ plugg₂) subst₀
        ∙ ap (λ q → q ∘ plugg₂) (subst₂-red ((f ∘ slot₀-iso .from) ∘ plugh₂))
        ∙ sym (assoc _ _ _)
        ∙ sym (assoc _ _ _)
        ∙ sym (assoc _ _ _)

      eq : transport (λ i → Hom (⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ i)) z)
              (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg) ∘ plugh₁)
            ≡ (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ)
                (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f ∘ plugh₂) ∘ plugg₂)
      eq =
          transport (λ i → Hom (⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ i)) z)
            (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg) ∘ plugh₁)
        ≡⟨ ap (λ ◆ → transport (λ i → Hom (⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ i)) z) (◆ ∘ plugh₁))
              subst₁ ⟩
          transport (λ i → Hom (⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ i)) z)
            (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁)
        ≡⟨ subst-⊗-red (interchangeₘ-boundary Θ Γ Μ Δ Κ) (ic-boundary-⊗ Θ Γ Μ Δ Κ)
              (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁) ⟩
          (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁) ∘ bdry-iso .from
        ≡⟨ sym (assoc _ _ _) ⟩
          ((f ∘ plugg) ∘ slot₁-iso .from) ∘ (plugh₁ ∘ bdry-iso .from)
        ≡⟨ sym (assoc _ _ _) ⟩
          (f ∘ plugg) ∘ (slot₁-iso .from ∘ (plugh₁ ∘ bdry-iso .from))
        ≡⟨ sym (assoc _ _ _) ⟩
          f ∘ (plugg ∘ (slot₁-iso .from ∘ (plugh₁ ∘ bdry-iso .from)))
        ≡⟨ ap (f ∘_) ic-plug-coherence ⟩
          f ∘ rest₂
        ≡⟨ sym RHS-red ⟩
          subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ)
            (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f ∘ plugh₂) ∘ plugg₂
        ∎



