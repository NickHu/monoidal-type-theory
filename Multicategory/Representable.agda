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
    (triangle-ρ← ; triangle-ρ→ ; triangle-λ← ; triangle-λ→ ; λ←≡ρ← ; λ→≡ρ→ ; ▶-assoc ; ◀-▶-comm)

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
      φ : ⊗-context (x ∷ Ξ) ≅ (⊗-context (x ∷ []) ⊗ ⊗-context Ξ)
      φ = ⊗-context-++ (x ∷ []) Ξ

      -- φ .from = ρ← x ◀ ⊗-context Ξ  (φ.from reduces to the LHS of the
      -- triangle identity triangle-α→).
      φ-from : φ .from ≡ ρ← x ◀ ⊗-context Ξ
      φ-from = triangle-α→

      -- (apply ρ←) ∘ (insert unit) is the identity: ρ← undoes the unit.
      mid≡id : (⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (φ .to)) ≡ id
      mid≡id =
          (⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (φ .to))
        ≡⟨ sym (▶.F-∘ _ _) ⟩
          ⊗-context Θ ▶ (((ρ← x) ◀ ⊗-context Ξ) ∘ φ .to)
        ≡⟨ ap (⊗-context Θ ▶_) (ap (_∘ φ .to) (sym φ-from)) ⟩
          ⊗-context Θ ▶ (φ .from ∘ φ .to)
        ≡⟨ ap (⊗-context Θ ▶_) (φ .invr) ⟩
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
            ∘ ((⊗-context Θ ▶ (φ .to)) ∘ split .to)
        ≡⟨ ap (split .from ∘_) (assoc _ _ _) ⟩
          split .from ∘ (((⊗-context Θ ▶ ((ρ← x) ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (φ .to))) ∘ split .to)
        ≡⟨ ap (λ p → split .from ∘ (p ∘ split .to)) mid≡id ⟩
          split .from ∘ (id ∘ split .to)
        ≡⟨ ap (split .from ∘_) (idl _) ⟩
          split .from ∘ split .to
        ≡⟨ split .invr ⟩
          id
        ∎

  Mc .idₘr {Γ = Γ} {z = z} f = to-pathp eq
    where
      -- λ-naturality: ρ←z ∘ λ←(at z⊗Unit) = λ←(at z) ∘ (Unit▶ρ←z).
      λ-nat-rho = unitor-l .Isoⁿ.from .is-natural (z ⊗ Unit) z (ρ← z)

      -- ρ-naturality: ρ←z ∘ (f◀Unit) = f ∘ ρ←(⊗Γ).
      ρ-nat-f = sym (unitor-r .Isoⁿ.from .is-natural (⊗-context Γ) z f)

      -- The three-way split ⊗(Γ++[]) ≅ Unit ⊗ (⊗Γ ⊗ Unit) and the ++-idr iso.
      split : ⊗-context (Γ ++ []) ≅ (Unit ⊗ (⊗-context Γ ⊗ Unit))
      split = ⊗-context-++-++ [] Γ []

      ρ-idr : ⊗-context (Γ ++ []) ≅ ⊗-context Γ
      ρ-idr = ⊗-context-++-idr Γ

      -- intro : ⊗Γ → Unit ⊗ (⊗Γ ⊗ Unit) introduces a unit on each side of ⊗Γ
      -- (the leading [] on the left, the trailing [] on the right).
      intro : Hom (⊗-context Γ) (Unit ⊗ (⊗-context Γ ⊗ Unit))
      intro = split .to ∘ ρ-idr .from

      -- λ→-naturality moves ρ-idr.from past the leading-unit λ→.
      λ→-nat
        : λ→ _ ∘ ρ-idr .from ≡ (Unit ▶ ρ-idr .from) ∘ λ→ (⊗-context Γ)
      λ→-nat =
        unitor-l .Isoⁿ.to .is-natural (⊗-context Γ) (⊗-context (Γ ++ [])) (ρ-idr .from)

      -- intro = (Unit ▶ ρ→(⊗Γ)) ∘ λ→(⊗Γ): the leading [] contributes λ→ and the
      -- trailing [] contributes ρ→ (via ⊗-context-++-[]-ρ).
      intro-eq : intro ≡ (Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
      intro-eq =
          intro
        ≡⟨⟩
          ((Unit ▶ (⊗-context-++ Γ []) .to) ∘ λ→ _) ∘ ρ-idr .from
        ≡⟨ sym (assoc _ _ _) ⟩
          (Unit ▶ (⊗-context-++ Γ []) .to) ∘ (λ→ _ ∘ ρ-idr .from)
        ≡⟨ ap ((Unit ▶ (⊗-context-++ Γ []) .to) ∘_) λ→-nat ⟩
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

      -- λ-naturality: λ←_z ∘ (Unit ▶ f) = f ∘ λ←(⊗Γ).
      λ-nat-f : λ← z ∘ (Unit ▶ f) ≡ f ∘ λ← (⊗-context Γ)
      λ-nat-f = unitor-l .Isoⁿ.from .is-natural (⊗-context Γ) z f

      -- The core equation.  plug [] Γ [] f unfolds to
      --   λ←(z⊗Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ split.to
      -- and split.to ∘ ρ-idr.from = intro, so after regrouping we reduce
      --   ρ←z ∘ λ←(z⊗Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ intro
      -- by a chain of naturality squares (λ-nat-rho, ρ-nat-f, λ-nat-f) and the
      -- unit coherences (▶.F-∘, sub, λ≅.invr) to f.
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
        ≡⟨ pulll (sym λ-nat-rho) ⟩
          (λ← z ∘ (Unit ▶ ρ← z)) ∘ ((Unit ▶ (f ◀ Unit)) ∘ intro)
        ≡⟨ sym (assoc _ _ _) ⟩
          λ← z ∘ ((Unit ▶ ρ← z) ∘ ((Unit ▶ (f ◀ Unit)) ∘ intro))
        ≡⟨ ap (λ← z ∘_) (pulll (sym (▶.F-∘ _ _))) ⟩
          λ← z ∘ ((Unit ▶ (ρ← z ∘ (f ◀ Unit))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (ap (_∘ intro) (ap (Unit ▶_) (sym ρ-nat-f))) ⟩
          λ← z ∘ ((Unit ▶ (f ∘ ρ← (⊗-context Γ))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (ap (_∘ intro) (▶.F-∘ _ _)) ⟩
          λ← z ∘ (((Unit ▶ f) ∘ (Unit ▶ ρ← (⊗-context Γ))) ∘ intro)
        ≡⟨ ap (λ← z ∘_) (sym (assoc _ _ _)) ⟩
          λ← z ∘ ((Unit ▶ f) ∘ ((Unit ▶ ρ← (⊗-context Γ)) ∘ intro))
        ≡⟨ ap (λ← z ∘_) (ap ((Unit ▶ f) ∘_) sub) ⟩
          λ← z ∘ ((Unit ▶ f) ∘ λ→ (⊗-context Γ))
        ≡⟨ pulll λ-nat-f ⟩
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
        ≡⟨ Hom-transport C (ap ⊗-context (++-idr Γ)) refl _ ⟩
          path→iso refl .to ∘ (ρ← z ∘ plug [] Γ [] f) ∘ path→iso (ap ⊗-context (++-idr Γ)) .from
        ≡⟨ ap (λ k → k ∘ (ρ← z ∘ plug [] Γ [] f) ∘ path→iso (ap ⊗-context (++-idr Γ)) .from)
               (ap (λ φ → φ .to) path→iso-refl) ⟩
          id ∘ (ρ← z ∘ plug [] Γ [] f) ∘ path→iso (ap ⊗-context (++-idr Γ)) .from
        ≡⟨ idl _ ⟩
          (ρ← z ∘ plug [] Γ [] f) ∘ path→iso (ap ⊗-context (++-idr Γ)) .from
        ≡⟨ ap ((ρ← z ∘ plug [] Γ [] f) ∘_)
               (ap (λ φ → φ .from) (⊗-context-++-idr-path Γ)) ⟩
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

      -- transport over Hom(⊗-)-by-domain reduces to precomposition with .from.
      transport-⊗-red : ∀ {A B : Ob} (q : A ≡ B) (M : Hom A z)
        → transport (λ i → Hom (q i) z) M ≡ M ∘ path→iso q .from
      transport-⊗-red q M =
          Hom-transport C q refl M
        ∙ ap (λ k → k ∘ M ∘ path→iso q .from) (ap (λ φ → φ .to) path→iso-refl)
        ∙ idl _

      subst-red : subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL)
                  ≡ (f ∘ plugL) ∘ slot-iso .from
      subst-red =
          transport-⊗-red (ap ⊗-context (slot-unbury Θ Φ y Ψ Ξ)) (f ∘ plugL)
        ∙ ap ((f ∘ plugL) ∘_) (ap (λ φ → φ .from) (slot-unbury-⊗ Θ Φ y Ψ Ξ))

      -- The f-free plug coherence (the pentagon): plugging h into the relocated
      -- slot of (f∘ₘg) equals plugging (g∘ₘh) into f's slot.  f is cancelled by
      -- `ap (f ∘_)`; this is the residual that remains after transport reduction.
      -- Aliases for the plug's split/decompose isos (see `plug` definition):
      --   plug Θ Γ Ξ k = splitL.from ∘ (⊗Θ ▶ (k ◀ ⊗Ξ)) ∘ dec.to
      splitL = ⊗-context-++ Θ (x ∷ Ξ)
      decL   = ⊗-context-++-++ Θ (Φ ++ y ∷ Ψ) Ξ
      decR   = ⊗-context-++-++ Θ (Φ ++ Ρ ++ Ψ) Ξ

      -- g cancelled: decL.to ∘ slot-iso.from ∘ plugH ∘ bdry-iso.from
      --              = (⊗Θ ▶ (plugGH ◀ ⊗Ξ)) ∘ decR.to   (only h remains).
      -- Proved by induction on the prefix Θ: the slot/boundary isos are clean
      -- ▶-recursions, and dec/plug carry α→ corrections (as in F-α→'s cons).
      gfi : (Θ' : List Ob)
        → (⊗-context-++-++ Θ' (Φ ++ y ∷ Ψ) Ξ) .to
            ∘ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from
            ∘ plug (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from
          ≡ (⊗-context Θ' ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ (⊗-context-++-++ Θ' (Φ ++ Ρ ++ Ψ) Ξ) .to
      gfi []        = {!!}
      gfi (a ∷ Θ') = {!!}

      g-free : decL .to ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from
               ≡ (⊗-context Θ ▶ (plugGH ◀ ⊗-context Ξ)) ∘ decR .to
      g-free = gfi Θ

      -- (⊗Θ ▶ a) ∘ (⊗Θ ▶ b) = ⊗Θ ▶ (a ∘ b)  (▶.F-∘), then ◀.F-∘ inside.
      merge-▶ : (⊗-context Θ ▶ (g ◀ ⊗-context Ξ)) ∘ (⊗-context Θ ▶ (plugGH ◀ ⊗-context Ξ))
                ≡ ⊗-context Θ ▶ ((g ∘ plugGH) ◀ ⊗-context Ξ)
      merge-▶ =
          sym (▶.F-∘ (g ◀ ⊗-context Ξ) (plugGH ◀ ⊗-context Ξ))
        ∙ ap (⊗-context Θ ▶_) (sym (◀.F-∘ g plugGH))

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
        ≡⟨ ap (splitL .from ∘_) (assoc _ _ _ ∙ ap (_∘ decR .to) merge-▶) ⟩
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
        ≡⟨ (transport-⊗-red (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ))
                (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH)
            ∙ ap (λ φ → (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH) ∘ φ)
                (ap (λ ψ → ψ .from) (assocₘ-boundary-⊗ Θ Φ Ρ Ψ Ξ))) ⟩
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

      transport-⊗-red : ∀ {A B : Ob} (q : A ≡ B) (M : Hom A z)
        → transport (λ i → Hom (q i) z) M ≡ M ∘ path→iso q .from
      transport-⊗-red q M =
          Hom-transport C q refl M
        ∙ ap (λ k → k ∘ M ∘ path→iso q .from) (ap (λ φ → φ .to) path→iso-refl)
        ∙ idl _

      subst₀ : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f
               ≡ f ∘ slot₀-iso .from
      subst₀ =
          transport-⊗-red (ap ⊗-context (interchange-slot₀ Θ x Μ y Κ)) f
        ∙ ap (f ∘_) (ap (λ φ → φ .from) (ic-slot₀-⊗ Θ x Μ y Κ))

      subst₁ : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg)
               ≡ (f ∘ plugg) ∘ slot₁-iso .from
      subst₁ =
          transport-⊗-red (ap ⊗-context (interchange-slot₁ Θ Γ Μ y Κ)) (f ∘ plugg)
        ∙ ap ((f ∘ plugg) ∘_) (ap (λ φ → φ .from) (ic-slot₁-⊗ Θ Γ Μ y Κ))

      subst₂-red : (M : Hom (⊗-context ((Θ ++ x ∷ Μ) ++ Δ ++ Κ)) z)
        → subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ) M ≡ M ∘ slot₂-iso .from
      subst₂-red M =
          transport-⊗-red (ap ⊗-context (interchange-slot₂ Θ x Μ Δ Κ)) M
        ∙ ap (M ∘_) (ap (λ φ → φ .from) (ic-slot₂-⊗ Θ x Μ Δ Κ))

      -- the f-free bifunctoriality coherence (the hard piece).
      ic-plug-coherence
        :   plugg ∘ slot₁-iso .from ∘ plugh₁ ∘ bdry-iso .from
        ≡ slot₀-iso .from ∘ plugh₂ ∘ slot₂-iso .from ∘ plugg₂
      ic-plug-coherence = {!!}

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
        ≡⟨ (transport-⊗-red (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ))
                (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁)
            ∙ ap (λ φ → (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁) ∘ φ)
                (ap (λ ψ → ψ .from) (ic-boundary-⊗ Θ Γ Μ Δ Κ))) ⟩
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


  ----------------------------------------------------------------------
  -- The monoidal-functor associativity hexagon for ⊗-context, stated
  -- standalone (the substance of "⊗-context is a strong monoidal functor").
  --   φ_{Γ,Δ} = (⊗-context-++ Γ Δ).from : ⊗Γ ⊗ ⊗Δ → ⊗(Γ++Δ)
  --   F-α→ : the associativity coherence (pure iso, no f/g/h).
  ----------------------------------------------------------------------
  φ : (Γ Δ : List Ob) → Hom (⊗-context Γ ⊗ ⊗-context Δ) (⊗-context (Γ ++ Δ))
  φ Γ Δ = (⊗-context-++ Γ Δ) .from

  -- Cons-reductions of the structure maps (definitional, hence refl):
  --   ++-assoc-⊗-iso (a ∷ Γ) Δ Ξ .to  =  a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to
  --   φ (a ∷ Γ) Δ                      =  (a ▶ φ Γ Δ) ∘ α→ (a , ⊗Γ , ⊗Δ)
  char-to-cons : (a : Ob) (Γ Δ Ξ : List Ob)
    → ++-assoc-⊗-iso (a ∷ Γ) Δ Ξ .to ≡ a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to
  char-to-cons a Γ Δ Ξ = refl

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
          (sym (unitor-l .Isoⁿ.from .is-natural (⊗-context Δ ⊗ ⊗-context Ξ) (⊗-context (Δ ++ Ξ)) (φ Δ Ξ)))
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
        (a ▶ (++-assoc-⊗-iso Γ Δ Ξ .to ∘ φ (Γ ++ Δ) Ξ ∘ (φ Γ Δ ◀ ⊗-context Ξ)))
      ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
      ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ)
      -- apply the induction hypothesis inside the ▶.
      ≡⟨ ap (λ m → (a ▶ m)
                 ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
                 ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ))
            (F-α→ Γ Δ Ξ) ⟩
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

