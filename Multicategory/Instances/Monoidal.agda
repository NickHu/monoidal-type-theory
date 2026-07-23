open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso; path→to-sym; Hom-transport; Hom-pathp-refll)
open import Cat.Functor.Naturality
import Cat.Functor.Base as FB
import Cat.Bi.Reasoning
open import Data.List
open import Data.List.Properties
import Multicategory.Representable as Rep

module Multicategory.Instances.Monoidal where

-- The representable multicategory of a monoidal category.
--
-- A multimorphism Γ ⟶ τ is a unary morphism (⊗ Γ) ⟶ τ in C, where ⊗ Γ
-- right-associates the tensor product over the (list) context and the empty
-- context is the tensor unit.  Because contexts are lists, ⊗-context is a plain
-- fold that reduces through _++_ definitionally — so the rebracketing isos used
-- in composition are reducing, and the law boundaries (plain list ≡s) are seen
-- through by ⊗-context.  This is what makes the laws tractable here, where they
-- were blocked in the Vec-based version.
-- The construction lives in a parametrised module so that both the
-- multicategory `Mc` and its representability proof `Mc-repr` (which needs the
-- local `plug`/`⊗-context` machinery) can be exposed at the top level.
module Repr {o h} (C : Precategory o h) (M : Monoidal-category C) where
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
  -- precomposition with the induced iso; the `subst`-over-⊗-context form
  -- composes it with a path→iso characterisation.  The inner substs in the
  -- assocₘ/interchangeₘ statements are reduced with subst-⊗-red; the laws'
  -- outer transports are discharged directly by Hom-pathp-refll.
  private
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
      sym (assoc _ _ _)
    ∙ ap (α← _ ∘_) (▶.collapse (⊗-context-++-[]-ρ Γ))
    ∙ sym triangle-ρ→

  ----------------------------------------------------------------------
  -- path→iso characterisations for the law transports.
  --
  -- Every law boundary in Multicategory.agda is a list-reassociation path
  -- built from refl and ++-assoc by `ap (a ∷_)` and `sym`, and ⊗-context is
  -- invariant under list reassociation: path→iso of each boundary is a
  -- cons-by-cons ▶-chain of id-iso.  A ⊗-chain packages that ▶-chain iso
  -- together with its path→iso characterisation, so the three combinators
  -- below (refl, cons, sym) generate every characterisation by one short
  -- recursion per boundary.  The .⊗iso projections reduce definitionally at
  -- cons (to ▶.F-map-iso of the tail), which the equational displays in the
  -- law proofs rely on.
  ----------------------------------------------------------------------

  record ⊗-chain {Γ Δ : List Ob} (p : Γ ≡ Δ) : Type h where
    constructor chain
    field
      ⊗iso : ⊗-context Γ ≅ ⊗-context Δ
      char : path→iso (ap ⊗-context p) ≡ ⊗iso

  open ⊗-chain

  chain-refl : {Γ : List Ob} → ⊗-chain (refl {x = Γ})
  chain-refl = chain id-iso path→iso-refl

  chain-∷ : (a : Ob) {Γ Δ : List Ob} {p : Γ ≡ Δ}
    → ⊗-chain p → ⊗-chain (ap (a ∷_) p)
  chain-∷ a {p = p} (chain i e) =
    chain (▶.F-map-iso i) (path→iso-ap-⊗ a (ap ⊗-context p) ∙ ap ▶.F-map-iso e)

  -- Isos agree when their .to legs do; the .to of path→iso (sym p) is the
  -- .from of path→iso p (1lab's path→to-sym).
  path→iso-sym : {A B : Ob} (p : A ≡ B) → path→iso (sym p) ≡ path→iso p Iso⁻¹
  path→iso-sym p = ≅-path (sym (path→to-sym C p))

  chain-sym : {Γ Δ : List Ob} {p : Γ ≡ Δ} → ⊗-chain p → ⊗-chain (sym p)
  chain-sym {p = p} (chain i e) =
    chain (i Iso⁻¹) (path→iso-sym (ap ⊗-context p) ∙ ap _Iso⁻¹ e)

  -- The shared base: ++-assoc.  (++-assoc-⊗-iso/-path is the public face,
  -- used by F-α→ below and by Multicategory.Instances.Monoidal.Coherence.)
  ++-assoc-chain : (Φ Ψ Ξ : List Ob) → ⊗-chain (++-assoc Φ Ψ Ξ)
  ++-assoc-chain []      Ψ Ξ = chain-refl
  ++-assoc-chain (a ∷ Φ) Ψ Ξ = chain-∷ a (++-assoc-chain Φ Ψ Ξ)

  ++-assoc-⊗-iso : (Φ Ψ Ξ : List Ob)
    → ⊗-context ((Φ ++ Ψ) ++ Ξ) ≅ ⊗-context (Φ ++ (Ψ ++ Ξ))
  ++-assoc-⊗-iso Φ Ψ Ξ = ++-assoc-chain Φ Ψ Ξ .⊗iso

  ++-assoc-⊗-path : (Φ Ψ Ξ : List Ob)
    → path→iso (ap ⊗-context (++-assoc Φ Ψ Ξ)) ≡ ++-assoc-⊗-iso Φ Ψ Ξ
  ++-assoc-⊗-path Φ Ψ Ξ = ++-assoc-chain Φ Ψ Ξ .char

  -- assocₘ boundaries: relocating the marked slot from Φ into (Θ ++ Φ), and
  -- the flattening of the composite boundary.  chain-sym absorbs what was an
  -- inner Ρ-recursion in assocₘ-flatten.
  slot-unbury-chain : (Θ Φ : List Ob) (y : Ob) (Ψ Ξ : List Ob)
    → ⊗-chain (slot-unbury Θ Φ y Ψ Ξ)
  slot-unbury-chain []      Φ y Ψ Ξ = ++-assoc-chain Φ (y ∷ Ψ) Ξ
  slot-unbury-chain (a ∷ Θ) Φ y Ψ Ξ = chain-∷ a (slot-unbury-chain Θ Φ y Ψ Ξ)

  assocₘ-flatten-chain : (Φ Ρ Ψ Ξ : List Ob) → ⊗-chain (assocₘ-flatten Φ Ρ Ψ Ξ)
  assocₘ-flatten-chain []      Ρ Ψ Ξ = chain-sym (++-assoc-chain Ρ Ψ Ξ)
  assocₘ-flatten-chain (a ∷ Φ) Ρ Ψ Ξ = chain-∷ a (assocₘ-flatten-chain Φ Ρ Ψ Ξ)

  assocₘ-boundary-chain : (Θ Φ Ρ Ψ Ξ : List Ob) → ⊗-chain (assocₘ-boundary Θ Φ Ρ Ψ Ξ)
  assocₘ-boundary-chain []      Φ Ρ Ψ Ξ = assocₘ-flatten-chain Φ Ρ Ψ Ξ
  assocₘ-boundary-chain (a ∷ Θ) Φ Ρ Ψ Ξ = chain-∷ a (assocₘ-boundary-chain Θ Φ Ρ Ψ Ξ)

  -- interchangeₘ boundaries (f has two slots x,y: Θ ++ x ∷ Μ ++ y ∷ Κ).
  -- slot₀, slot₂ and flatten are (sym of) ++-assoc paths outright, so their
  -- chains need no recursion of their own; slot₁ and the boundary recurse on
  -- the prefix Θ.
  ic-slot₀-chain : (Θ : List Ob) (x : Ob) (Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-chain (interchange-slot₀ Θ x Μ y Κ)
  ic-slot₀-chain Θ x Μ y Κ = chain-sym (++-assoc-chain Θ (x ∷ Μ) (y ∷ Κ))

  ic-slot₁-chain : (Θ Γ Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-chain (interchange-slot₁ Θ Γ Μ y Κ)
  ic-slot₁-chain []      Γ Μ y Κ = chain-sym (++-assoc-chain Γ Μ (y ∷ Κ))
  ic-slot₁-chain (a ∷ Θ) Γ Μ y Κ = chain-∷ a (ic-slot₁-chain Θ Γ Μ y Κ)

  ic-slot₂-chain : (Θ : List Ob) (x : Ob) (Μ Δ Κ : List Ob)
    → ⊗-chain (interchange-slot₂ Θ x Μ Δ Κ)
  ic-slot₂-chain Θ x Μ Δ Κ = ++-assoc-chain Θ (x ∷ Μ) (Δ ++ Κ)

  ic-flatten-chain : (Γ Μ Δ Κ : List Ob) → ⊗-chain (interchange-flatten Γ Μ Δ Κ)
  ic-flatten-chain Γ Μ Δ Κ = ++-assoc-chain Γ Μ (Δ ++ Κ)

  ic-boundary-chain : (Θ Γ Μ Δ Κ : List Ob) → ⊗-chain (interchangeₘ-boundary Θ Γ Μ Δ Κ)
  ic-boundary-chain []      Γ Μ Δ Κ = ic-flatten-chain Γ Μ Δ Κ
  ic-boundary-chain (a ∷ Θ) Γ Μ Δ Κ = chain-∷ a (ic-boundary-chain Θ Γ Μ Δ Κ)

  -- Iso aliases: the names the law proofs' equational displays use.
  slot-unbury-iso : (Θ Φ : List Ob) (y : Ob) (Ψ Ξ : List Ob)
    → ⊗-context (Θ ++ ((Φ ++ y ∷ Ψ) ++ Ξ)) ≅ ⊗-context ((Θ ++ Φ) ++ y ∷ (Ψ ++ Ξ))
  slot-unbury-iso Θ Φ y Ψ Ξ = slot-unbury-chain Θ Φ y Ψ Ξ .⊗iso

  assocₘ-flatten-iso : (Φ Ρ Ψ Ξ : List Ob)
    → ⊗-context (Φ ++ Ρ ++ (Ψ ++ Ξ)) ≅ ⊗-context ((Φ ++ Ρ ++ Ψ) ++ Ξ)
  assocₘ-flatten-iso Φ Ρ Ψ Ξ = assocₘ-flatten-chain Φ Ρ Ψ Ξ .⊗iso

  assocₘ-boundary-iso : (Θ Φ Ρ Ψ Ξ : List Ob)
    → ⊗-context ((Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ)) ≅ ⊗-context (Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ))
  assocₘ-boundary-iso Θ Φ Ρ Ψ Ξ = assocₘ-boundary-chain Θ Φ Ρ Ψ Ξ .⊗iso

  ic-slot₀-iso : (Θ : List Ob) (x : Ob) (Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-context (Θ ++ x ∷ Μ ++ y ∷ Κ) ≅ ⊗-context ((Θ ++ x ∷ Μ) ++ y ∷ Κ)
  ic-slot₀-iso Θ x Μ y Κ = ic-slot₀-chain Θ x Μ y Κ .⊗iso

  ic-slot₁-iso : (Θ Γ Μ : List Ob) (y : Ob) (Κ : List Ob)
    → ⊗-context (Θ ++ Γ ++ Μ ++ y ∷ Κ) ≅ ⊗-context ((Θ ++ Γ ++ Μ) ++ y ∷ Κ)
  ic-slot₁-iso Θ Γ Μ y Κ = ic-slot₁-chain Θ Γ Μ y Κ .⊗iso

  ic-slot₂-iso : (Θ : List Ob) (x : Ob) (Μ Δ Κ : List Ob)
    → ⊗-context ((Θ ++ x ∷ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Θ ++ x ∷ (Μ ++ Δ ++ Κ))
  ic-slot₂-iso Θ x Μ Δ Κ = ic-slot₂-chain Θ x Μ Δ Κ .⊗iso

  ic-flatten-iso : (Γ Μ Δ Κ : List Ob)
    → ⊗-context ((Γ ++ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Γ ++ (Μ ++ Δ ++ Κ))
  ic-flatten-iso Γ Μ Δ Κ = ic-flatten-chain Γ Μ Δ Κ .⊗iso

  ic-boundary-iso : (Θ Γ Μ Δ Κ : List Ob)
    → ⊗-context ((Θ ++ Γ ++ Μ) ++ Δ ++ Κ) ≅ ⊗-context (Θ ++ Γ ++ (Μ ++ Δ ++ Κ))
  ic-boundary-iso Θ Γ Μ Δ Κ = ic-boundary-chain Θ Γ Μ Δ Κ .⊗iso

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
        ∘ ⌜ (a ▶ (⊗-context Ω ▶ (g ◀ ⊗-context Ξ'))) ∘ (a ▶ (⊗-context-++-++ Ω Γ Ξ') .to) ⌝
    ≡⟨ ap! (sym (▶.F-∘ _ _)) ⟩
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
        ∘ ⌜ λ← (⊗-context Γ ⊗ ⊗-context Ξ') ∘ (λ→ (⊗-context Γ ⊗ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to) ⌝
    ≡⟨ ap! (cancell (λ≅ .invr)) ⟩
      (g ◀ ⊗-context Ξ') ∘ (⊗-context-++ Γ Ξ') .to
    ∎

  ----------------------------------------------------------------------
  -- The shared cons-step of the prefix inductions (plug-assoc-nil, plug-assoc,
  -- plug-shift, plug-interchange): rewrite plug (b ∷ Ω) by plug-cons, merge
  -- the four ▶-factors, apply the induction hypothesis inside the ▶, unmerge
  -- once, and slide the naturality square k ∘ (b ▶ X) ≡ X' ∘ k'.
  ----------------------------------------------------------------------

  -- b ▶_ distributed over a 4-composite.
  ▶-∘₄ : (b : Ob) {A₀ A₁ A₂ A₃ A₄ : Ob}
    (p : Hom A₃ A₄) (q : Hom A₂ A₃) (r : Hom A₁ A₂) (s : Hom A₀ A₁)
    → b ▶ (p ∘ q ∘ r ∘ s) ≡ (b ▶ p) ∘ (b ▶ q) ∘ (b ▶ r) ∘ (b ▶ s)
  ▶-∘₄ b p q r s =
    ▶.F-∘ _ _ ∙ ap ((b ▶ p) ∘_) (▶.F-∘ _ _ ∙ ap ((b ▶ q) ∘_) (▶.F-∘ _ _))

  cons-step : {b : Ob} {A₀ A₁ A₂ A₃ A₄ W U V : Ob}
    {s : Hom A₃ A₄} {i₁ : Hom A₂ A₃} {P : Hom A₁ A₂} {i₂ : Hom A₀ A₁}
    {X : Hom W A₄} {t : Hom A₀ W}
    {k : Hom (b ⊗ A₄) V} {k' : Hom (b ⊗ W) U} {X' : Hom U V}
    → s ∘ i₁ ∘ P ∘ i₂ ≡ X ∘ t
    → k ∘ (b ▶ X) ≡ X' ∘ k'
    → (k ∘ (b ▶ s)) ∘ (b ▶ i₁) ∘ (b ▶ P) ∘ (b ▶ i₂) ≡ X' ∘ k' ∘ (b ▶ t)
  cons-step {b = b} {s = s} {i₁} {P} {i₂} ih nat =
      sym (assoc _ _ _)
    ∙ ap (_ ∘_) (sym (▶-∘₄ b s i₁ P i₂) ∙ ap (b ▶_) ih ∙ ▶.F-∘ _ _)
    ∙ extendl nat

  -- The k-free variant, for plug-interchange's cons (all four factors are
  -- ▶-whiskered; no α← correction, no naturality square).
  ▶-weave₄ : (b : Ob) {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ : Ob}
    {p : Hom A₃ A₄} {q : Hom A₂ A₃} {r : Hom A₁ A₂} {s : Hom A₀ A₁}
    {p' : Hom B₃ A₄} {q' : Hom B₂ B₃} {r' : Hom B₁ B₂} {s' : Hom A₀ B₁}
    → p ∘ q ∘ r ∘ s ≡ p' ∘ q' ∘ r' ∘ s'
    → (b ▶ p) ∘ (b ▶ q) ∘ (b ▶ r) ∘ (b ▶ s)
    ≡ (b ▶ p') ∘ (b ▶ q') ∘ (b ▶ r') ∘ (b ▶ s')
  ▶-weave₄ b {p = p} {q} {r} {s} {p'} {q'} {r'} {s'} eq =
    sym (▶-∘₄ b p q r s) ∙ ap (b ▶_) eq ∙ ▶-∘₄ b p' q' r' s'

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
      ∘ ⌜ ((a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , ⊗-context Δ)) ◀ ⊗-context Ξ ⌝
      -- coh1: distribute ◀ over the whiskered α2, use ◀-▶-comm (middle-slot α→
      -- naturality) to push φ Γ Δ past the outer α→, then merge the ▶-layer.
      -- No IH — pure structure.
      ≡⟨ ap! (◀.F-∘ _ _) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ ((a ▶ φ (Γ ++ Δ) Ξ) ∘ α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ))
      ∘ (((a ▶ φ Γ Δ) ◀ ⊗-context Ξ) ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ))
      ≡⟨ ap ((a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to) ∘_)
            (sym (assoc _ _ _) ∙ ap ((a ▶ φ (Γ ++ Δ) Ξ) ∘_) (assoc _ _ _)) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ (a ▶ φ (Γ ++ Δ) Ξ)
      ∘ ( ⌜ α→ (a , ⊗-context (Γ ++ Δ) , ⊗-context Ξ) ∘ ((a ▶ φ Γ Δ) ◀ ⊗-context Ξ) ⌝
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) )
      ≡⟨ ap! ((◀-▶-comm {f = ⊗-context Ξ} {g = a}) .Isoⁿ.to .is-natural _ _ (φ Γ Δ)) ⟩
        (a ▶ ++-assoc-⊗-iso Γ Δ Ξ .to)
      ∘ (a ▶ φ (Γ ++ Δ) Ξ)
      ∘ ⌜ ((a ▶ (φ Γ Δ ◀ ⊗-context Ξ)) ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ))
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) ⌝
      ≡⟨ ap! (sym (assoc _ _ _)) ⟩
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
      ∘ ⌜ (a ▶ α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ))
        ∘ α→ (a , ⊗-context Γ ⊗ ⊗-context Δ , ⊗-context Ξ)
        ∘ (α→ (a , ⊗-context Γ , ⊗-context Δ) ◀ ⊗-context Ξ) ⌝
      ≡⟨ ap! pentagon-α→ ⟩
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
      -- regrouping folds φ (a ∷ Γ) (Δ ++ Ξ) back (definitional, φ-cons).
      ≡⟨ assoc _ _ _ ⟩
        φ (a ∷ Γ) (Δ ++ Ξ) ∘ ((a ⊗ ⊗-context Γ) ▶ φ Δ Ξ) ∘ α→ (a ⊗ ⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      ∎

  -- The .to-direction of the hexagon (every factor inverted; a swizzle of
  -- F-α→, no induction of its own).  Used for the assocₘ base plug-assoc-nil [].
  F-α→-to : (Γ Δ Ξ : List Ob)
    →   (⊗-context Γ ▶ (⊗-context-++ Δ Ξ) .to)
      ∘ (⊗-context-++ Γ (Δ ++ Ξ)) .to
      ∘ (++-assoc-⊗-iso Γ Δ Ξ) .to
    ≡   α→ (⊗-context Γ , ⊗-context Δ , ⊗-context Ξ)
      ∘ ((⊗-context-++ Γ Δ) .to ◀ ⊗-context Ξ)
      ∘ (⊗-context-++ (Γ ++ Δ) Ξ) .to
  F-α→-to Γ Δ Ξ =
      ap ((⊗-context Γ ▶ P₄ .to) ∘_)
         ( swizzle (F-α→ Γ Δ Ξ) (◀.cancel-inner (P₁ .invr) ∙ P₂ .invr) (P₃ .invl)
         ∙ sym (assoc _ _ _) )
    ∙ ▶.cancell (P₄ .invl)
    where
      P₁ = ⊗-context-++ Γ Δ
      P₂ = ⊗-context-++ (Γ ++ Δ) Ξ
      P₃ = ⊗-context-++ Γ (Δ ++ Ξ)
      P₄ = ⊗-context-++ Δ Ξ

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

      -- plug with g = ρ← is the identity: ψ .from IS ρ← x ◀ ⊗Ξ (the monoidal
      -- triangle, triangle-α→), so the whiskered middle (⊗Θ ▶ _) annihilates
      -- and the outer split cancels itself.
      plug-ρ : plug Θ (x ∷ []) Ξ (ρ← x) ≡ id
      plug-ρ =
          ap (split .from ∘_)
             (cancell (▶.annihilate (ap (_∘ ψ .to) (sym triangle-α→) ∙ ψ .invr)))
        ∙ split .invr

  -- Right identity: the PathP over ++-idr Γ is precomposition with the
  -- boundary iso (Hom-pathp-refll); ⊗-context-++-idr-path characterises that
  -- iso, and the residual plug-unit-core reduces by the unit coherences.
  Mc .idₘr {Γ = Γ} {z = z} f = Hom-pathp-refll C
    ( ap ((ρ← z ∘ plug [] Γ [] f) ∘_)
         (ap (λ i → i .from) (⊗-context-++-idr-path Γ))
    ∙ plug-unit-core )
    where
      ρ-idr : ⊗-context (Γ ++ []) ≅ ⊗-context Γ
      ρ-idr = ⊗-context-++-idr Γ

      -- intro : ⊗Γ → Unit ⊗ (⊗Γ ⊗ Unit) introduces a unit on each side of ⊗Γ:
      -- the leading [] contributes λ→, the trailing [] contributes ρ→ (via
      -- ⊗-context-++-[]-ρ, slid across λ→'s naturality square).
      intro : Hom (⊗-context Γ) (Unit ⊗ (⊗-context Γ ⊗ Unit))
      intro = (⊗-context-++-++ [] Γ []) .to ∘ ρ-idr .from

      intro-eq : intro ≡ (Unit ▶ ρ→ (⊗-context Γ)) ∘ λ→ (⊗-context Γ)
      intro-eq =
          sym (assoc _ _ _)
        ∙ ap ((Unit ▶ (⊗-context-++ Γ []) .to) ∘_) (λ→nat (ρ-idr .from))
        ∙ ▶.pulll (⊗-context-++-[]-ρ Γ)

      -- (Unit ▶ ρ←(⊗Γ)) ∘ intro = λ→(⊗Γ): ρ← undoes the ρ→ intro inserted.
      unit-cancel : (Unit ▶ ρ← (⊗-context Γ)) ∘ intro ≡ λ→ (⊗-context Γ)
      unit-cancel =
        ap ((Unit ▶ ρ← (⊗-context Γ)) ∘_) intro-eq ∙ ▶.cancell (ρ≅ .invr)

      -- The core equation.  plug [] Γ [] f unfolds to
      --   λ←(z⊗Unit) ∘ (Unit ▶ (f ◀ Unit)) ∘ split.to,
      -- and split.to ∘ ρ-idr.from = intro; slide ρ← z inward across the
      -- unitor naturality squares (λ←nat, ρ←nat) and cancel the units
      -- (unit-cancel, λ≅.invr).
      plug-unit-core : (ρ← z ∘ plug [] Γ [] f) ∘ ρ-idr .from ≡ f
      plug-unit-core =
          sym (assoc _ _ _)
        ∙ ap (ρ← z ∘_)
             (sym (assoc _ _ _) ∙ ap (λ← (z ⊗ Unit) ∘_) (sym (assoc _ _ _)))
        ∙ pulll (sym (λ←nat (ρ← z)))
        ∙ sym (assoc _ _ _)
        ∙ ap (λ← z ∘_)
            ( ▶.pulll (ρ←nat f)
            ∙ ▶.pushl refl
            ∙ ap ((Unit ▶ f) ∘_) unit-cancel )
        ∙ pulll (λ←nat f)
        ∙ cancelr (λ≅ .invr)

  Mc .assocₘ {Θ = Θ} {Ξ = Ξ} {Φ = Φ} {Ψ = Ψ} {Ρ = Ρ} {x = x} {y = y} {z = z} f g h =
    Hom-pathp-refll C eq
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
      subst-red = subst-⊗-red (slot-unbury Θ Φ y Ψ Ξ) (slot-unbury-chain Θ Φ y Ψ Ξ .char) (f ∘ plugL)

      -- The f-free plug coherence (the pentagon): plugging h into the relocated
      -- slot of (f∘ₘg) equals plugging (g∘ₘh) into f's slot.  f is cancelled by
      -- `ap (f ∘_)`; this is the residual that remains after transport reduction.
      -- Aliases for the plug's split/decompose isos (see `plug` definition):
      --   plug Θ Γ Ξ k = splitL.from ∘ (⊗Θ ▶ (k ◀ ⊗Ξ)) ∘ dec.to
      splitL = ⊗-context-++ Θ (x ∷ Ξ)
      decL   = ⊗-context-++-++ Θ (Φ ++ y ∷ Ψ) Ξ
      decR   = ⊗-context-++-++ Θ (Φ ++ Ρ ++ Ψ) Ξ

      -- The Θ=[] core, generalised over Φ so it can recurse: the 2-way-split
      -- version of plug-assoc (⊗-context-++ / ++-assoc-⊗ / assocₘ-flatten in
      -- place of the -++-++ / slot-unbury / assocₘ-boundary isos).
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
        -- (assocₘ-flatten-iso [] Ρ Ψ Ξ).from is (++-assoc-⊗-iso Ρ Ψ Ξ).to and
        -- (++-assoc-⊗-iso [] (y ∷ Ψ) Ξ).from is id, definitionally (chains).
        ≡⟨ ap! (plug-nil Ρ (Ψ ++ Ξ) h) ⟩
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ id
            ∘ ((h ◀ ⊗-context (Ψ ++ Ξ)) ∘ (⊗-context-++ Ρ (Ψ ++ Ξ)) .to)
            ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to
        ≡⟨ ap ((⊗-context-++ (y ∷ Ψ) Ξ) .to ∘_) (idl _) ⟩
          (⊗-context-++ (y ∷ Ψ) Ξ) .to
            ∘ ( ((h ◀ ⊗-context (Ψ ++ Ξ)) ∘ (⊗-context-++ Ρ (Ψ ++ Ξ)) .to)
              ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to )
        -- unfold ψ(y∷Ψ) = α← ∘ (y ▶ ψ Ψ Ξ) (⊗-context-++ cons, definitional),
        -- pull α← out.
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
              ∘ ⌜ (⊗-context Ρ ▶ (⊗-context-++ Ψ Ξ) .to)
                ∘ ((⊗-context-++ Ρ (Ψ ++ Ξ)) .to ∘ (++-assoc-⊗-iso Ρ Ψ Ξ) .to) ⌝ )
        -- the h-free tail is the .to-hexagon F-α→-to Ρ Ψ Ξ.
        ≡⟨ ap! (F-α→-to Ρ Ψ Ξ) ⟩
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
      -- Cons: plug-cons, then the shared cons-step (naturality square:
      -- ◀-▶-comm slides the ▶-whiskered plug past the α← that the split's
      -- cons unfolding contributes), then fold plug (b ∷ Φ') back.
      plug-assoc-nil (b ∷ Φ') =
          ap (λ w → (⊗-context-++ ((b ∷ Φ') ++ y ∷ Ψ) Ξ) .to
                  ∘ (b ▶ (++-assoc-⊗-iso Φ' (y ∷ Ψ) Ξ) .from)
                  ∘ w
                  ∘ (b ▶ (assocₘ-flatten-iso Φ' Ρ Ψ Ξ) .from))
             (plug-cons b Φ' Ρ (Ψ ++ Ξ) h)
        ∙ cons-step (plug-assoc-nil Φ')
            ((◀-▶-comm {f = ⊗-context Ξ} {g = b}) .Isoⁿ.from .is-natural _ _
              (plug Φ' Ρ Ψ h))
        ∙ ap (λ w → (w ◀ ⊗-context Ξ) ∘ (⊗-context-++ ((b ∷ Φ') ++ Ρ ++ Ψ) Ξ) .to)
             (sym (plug-cons b Φ' Ρ Ψ h))

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
      -- plug-assoc-nil, whose own base Φ=[] unfolds plug (plug-nil) and bottoms
      -- out in the .to-hexagon F-α→-to plus α→ first-slot naturality.
      plug-assoc [] =
          ⌜ (⊗-context-++-++ [] (Φ ++ y ∷ Ψ) Ξ) .to ⌝
            ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
            ∘ plug Φ Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from
        ≡⟨ ap! (split3-nil (Φ ++ y ∷ Ψ) Ξ) ⟩
          (λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ y ∷ Ψ) Ξ) .to)
            ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
            ∘ plug Φ Ρ (Ψ ++ Ξ) h
            ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from
        ≡⟨ sym (assoc _ _ _) ⟩
          λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ ⌜ (⊗-context-++ (Φ ++ y ∷ Ψ) Ξ) .to
              ∘ (++-assoc-⊗-iso Φ (y ∷ Ψ) Ξ) .from
              ∘ plug Φ Ρ (Ψ ++ Ξ) h
              ∘ (assocₘ-flatten-iso Φ Ρ Ψ Ξ) .from ⌝
        ≡⟨ ap! (plug-assoc-nil Φ) ⟩
          λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ)
            ∘ ((plug Φ Ρ Ψ h ◀ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to)
        ≡⟨ assoc _ _ _ ⟩
          ⌜ λ→ (⊗-context (Φ ++ y ∷ Ψ) ⊗ ⊗-context Ξ) ∘ (plug Φ Ρ Ψ h ◀ ⊗-context Ξ) ⌝
            ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to
        ≡⟨ ap! (λ→nat (plugGH ◀ ⊗-context Ξ)) ⟩
          ((Unit ▶ (plugGH ◀ ⊗-context Ξ)) ∘ λ→ (⊗-context (Φ ++ Ρ ++ Ψ) ⊗ ⊗-context Ξ))
            ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to
        ≡⟨ sym (assoc _ _ _) ⟩
          (Unit ▶ (plugGH ◀ ⊗-context Ξ))
            ∘ ⌜ λ→ (⊗-context (Φ ++ Ρ ++ Ψ) ⊗ ⊗-context Ξ) ∘ (⊗-context-++ (Φ ++ Ρ ++ Ψ) Ξ) .to ⌝
        ≡⟨ ap! (sym (split3-nil (Φ ++ Ρ ++ Ψ) Ξ)) ⟩
          (⊗-context [] ▶ (plugGH ◀ ⊗-context Ξ)) ∘ (⊗-context-++-++ [] (Φ ++ Ρ ++ Ψ) Ξ) .to
        ∎
      -- Cons: split3-cons + plug-cons expose the four ▶-factors, cons-step
      -- runs the IH (naturality square: ▶-assoc slides the doubly-whiskered
      -- plugGH past the α← correction), and split3-cons folds back.
      plug-assoc (a ∷ Θ') =
          ap₂ (λ u w → u
                     ∘ (a ▶ (slot-unbury-iso Θ' Φ y Ψ Ξ) .from)
                     ∘ w
                     ∘ (a ▶ (assocₘ-boundary-iso Θ' Φ Ρ Ψ Ξ) .from))
              (split3-cons a Θ' (Φ ++ y ∷ Ψ) Ξ)
              (plug-cons a (Θ' ++ Φ) Ρ (Ψ ++ Ξ) h)
        ∙ cons-step (plug-assoc Θ')
            ((▶-assoc {f = a} {g = ⊗-context Θ'}) .Isoⁿ.from .is-natural _ _
              (plugGH ◀ ⊗-context Ξ))
        ∙ ap ((⊗-context (a ∷ Θ') ▶ (plugGH ◀ ⊗-context Ξ)) ∘_)
             (sym (split3-cons a Θ' (Φ ++ Ρ ++ Ψ) Ξ))

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
               ∘ ⌜ decL .to ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from ⌝)
        ≡⟨ ap! g-free ⟩
          splitL .from
            ∘ ((⊗-context Θ ▶ (g ◀ ⊗-context Ξ))
               ∘ ((⊗-context Θ ▶ (plugGH ◀ ⊗-context Ξ)) ∘ decR .to))
        ≡⟨ ap (splitL .from ∘_) (assoc _ _ _ ∙ ap (_∘ decR .to) (▶.collapse (sym (◀.F-∘ g plugGH)))) ⟩
          splitL .from ∘ ((⊗-context Θ ▶ ((g ∘ plugGH) ◀ ⊗-context Ξ)) ∘ decR .to)
        ≡⟨⟩
          plugR
        ∎

      -- The PathP over the assocₘ boundary is precomposition with the boundary
      -- iso (Hom-pathp-refll); the chain characterisations turn the inner
      -- subst and the boundary path→iso into the ▶-chain isos, leaving the
      -- f-free plug-coherence.
      eq : (subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL) ∘ plugH)
             ∘ path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)) .from
           ≡ f ∘ plugR
      eq =
          (subst (λ Ω → Hom (⊗-context Ω) z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ plugL) ∘ plugH)
            ∘ path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)) .from
        ≡⟨ ap (λ u → (u ∘ plugH) ∘ path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)) .from)
              subst-red ⟩
          (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH)
            ∘ ⌜ path→iso (ap ⊗-context (assocₘ-boundary Θ Φ Ρ Ψ Ξ)) .from ⌝
        ≡⟨ ap! (ap (λ i → i .from) (assocₘ-boundary-chain Θ Φ Ρ Ψ Ξ .char)) ⟩
          (((f ∘ plugL) ∘ slot-iso .from) ∘ plugH) ∘ bdry-iso .from
        ≡⟨ sym (assoc _ _ _) ∙ sym (assoc _ _ _) ∙ sym (assoc _ _ _) ⟩
          f ∘ ⌜ plugL ∘ slot-iso .from ∘ plugH ∘ bdry-iso .from ⌝
        ≡⟨ ap! plug-coherence ⟩
          f ∘ plugR
        ∎

  Mc .interchangeₘ {Θ = Θ} {Μ = Μ} {Κ = Κ} {Γ = Γ} {Δ = Δ} {x = x} {y = y} {z = z} f g h =
    Hom-pathp-refll C eq
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
      subst₀ = subst-⊗-red (interchange-slot₀ Θ x Μ y Κ) (ic-slot₀-chain Θ x Μ y Κ .char) f

      subst₁ : subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg)
               ≡ (f ∘ plugg) ∘ slot₁-iso .from
      subst₁ = subst-⊗-red (interchange-slot₁ Θ Γ Μ y Κ) (ic-slot₁-chain Θ Γ Μ y Κ .char) (f ∘ plugg)

      subst₂-red : (M : Hom (⊗-context ((Θ ++ x ∷ Μ) ++ Δ ++ Κ)) z)
        → subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ) M ≡ M ∘ slot₂-iso .from
      subst₂-red = subst-⊗-red (interchange-slot₂ Θ x Μ Δ Κ) (ic-slot₂-chain Θ x Μ Δ Κ .char)

      -- The g-free remainder of the interchange base (Θ=[]), generalised over Γ
      -- so it can recurse: relates plug (Γ++Μ) h to (⊗Γ ▶ plug Μ h).  Since g has
      -- been factored out, Γ-induction is legitimate (h, plug Μ h are Γ-fixed).
      -- Cons is the shared cons-step; base Γ=[] is left-unitor naturality.
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
      -- Cons: plug-cons, then the shared cons-step (naturality square:
      -- ▶-assoc slides the doubly-whiskered plug past the α← that the
      -- ⊗-context-++ cons unfolding contributes).  Nothing to fold back:
      -- both RHS factors reduce at (b ∷ Γ') definitionally.
      plug-shift (b ∷ Γ') =
          ap (λ w → (⊗-context-++ (b ∷ Γ') (Μ ++ y ∷ Κ)) .to
                  ∘ (b ▶ (ic-slot₁-iso [] Γ' Μ y Κ) .from)
                  ∘ w
                  ∘ (b ▶ (ic-flatten-iso Γ' Μ Δ Κ) .from))
             (plug-cons b (Γ' ++ Μ) Δ Κ h)
        ∙ cons-step (plug-shift Γ')
            ((▶-assoc {f = b} {g = ⊗-context Γ'}) .Isoⁿ.from .is-natural _ _
              (plug Μ Δ Κ h))

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
          ⌜ plug [] Γ (Μ ++ y ∷ Κ) g ⌝
            ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
            ∘ plug ([] ++ Γ ++ Μ) Δ Κ h
            ∘ (ic-boundary-iso [] Γ Μ Δ Κ) .from
        ≡⟨ ap! (plug-nil Γ (Μ ++ y ∷ Κ) g) ⟩
          ((g ◀ ⊗-context (Μ ++ y ∷ Κ)) ∘ (⊗-context-++ Γ (Μ ++ y ∷ Κ)) .to)
            ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
            ∘ plug (Γ ++ Μ) Δ Κ h
            ∘ (ic-flatten-iso Γ Μ Δ Κ) .from
        ≡⟨ sym (assoc _ _ _) ⟩
          (g ◀ ⊗-context (Μ ++ y ∷ Κ))
            ∘ ⌜ (⊗-context-++ Γ (Μ ++ y ∷ Κ)) .to
              ∘ (ic-slot₁-iso [] Γ Μ y Κ) .from
              ∘ plug (Γ ++ Μ) Δ Κ h
              ∘ (ic-flatten-iso Γ Μ Δ Κ) .from ⌝
        ≡⟨ ap! (plug-shift Γ) ⟩
          (g ◀ ⊗-context (Μ ++ y ∷ Κ))
            ∘ ((⊗-context Γ ▶ plug Μ Δ Κ h) ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to)
        ≡⟨ assoc _ _ _ ⟩
          ⌜ (g ◀ ⊗-context (Μ ++ y ∷ Κ)) ∘ (⊗-context Γ ▶ plug Μ Δ Κ h) ⌝
            ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to
        ≡⟨ ap! (sym (-⊗-.rlmap (plug Μ Δ Κ h) g)) ⟩
          ((x ▶ plug Μ Δ Κ h) ∘ (g ◀ ⊗-context (Μ ++ Δ ++ Κ)))
            ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to
        ≡⟨ sym (assoc _ _ _) ⟩
          (x ▶ plug Μ Δ Κ h)
            ∘ ⌜ (g ◀ ⊗-context (Μ ++ Δ ++ Κ)) ∘ (⊗-context-++ Γ (Μ ++ Δ ++ Κ)) .to ⌝
        ≡⟨ ap! (sym (plug-nil Γ (Μ ++ Δ ++ Κ) g)) ⟩
          ⌜ x ▶ plug Μ Δ Κ h ⌝ ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ≡⟨ ap! (sym (plug-cons x Μ Δ Κ h)) ⟩
          plug (x ∷ Μ) Δ Κ h ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ≡⟨ ap (plug (x ∷ Μ) Δ Κ h ∘_) (sym (idl _)) ∙ sym (idl _) ⟩
          (ic-slot₀-iso [] x Μ y Κ) .from
            ∘ plug (x ∷ Μ) Δ Κ h
            ∘ (ic-slot₂-iso [] x Μ Δ Κ) .from
            ∘ plug [] Γ (Μ ++ Δ ++ Κ) g
        ∎
      -- Cons: both plugs unfold by plug-cons, ▶-weave₄ runs the IH inside the
      -- ▶ (no α corrections: every factor is a ▶), and the two plugs fold
      -- back one at a time (two sequential aps).
      plug-interchange (a ∷ Θ') =
          ap₂ (λ u w → u ∘ (a ▶ (ic-slot₁-iso Θ' Γ Μ y Κ) .from)
                         ∘ w ∘ (a ▶ (ic-boundary-iso Θ' Γ Μ Δ Κ) .from))
              (plug-cons a Θ' Γ (Μ ++ y ∷ Κ) g)
              (plug-cons a (Θ' ++ Γ ++ Μ) Δ Κ h)
        ∙ ▶-weave₄ a (plug-interchange Θ')
        ∙ ap (λ u → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
                  ∘ u ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from)
                  ∘ (a ▶ plug Θ' Γ (Μ ++ Δ ++ Κ) g))
             (sym (plug-cons a (Θ' ++ x ∷ Μ) Δ Κ h))
        ∙ ap (λ w → (a ▶ (ic-slot₀-iso Θ' x Μ y Κ) .from)
                  ∘ plug ((a ∷ Θ') ++ x ∷ Μ) Δ Κ h
                  ∘ (a ▶ (ic-slot₂-iso Θ' x Μ Δ Κ) .from) ∘ w)
             (sym (plug-cons a Θ' Γ (Μ ++ Δ ++ Κ) g))

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

      -- As in assocₘ: the PathP is precomposition with the boundary iso, the
      -- chains characterise it, and the residual is ic-plug-coherence.
      eq : (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg) ∘ plugh₁)
             ∘ path→iso (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ)) .from
           ≡ subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ)
               (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f ∘ plugh₂) ∘ plugg₂
      eq =
          (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₁ Θ Γ Μ y Κ) (f ∘ plugg) ∘ plugh₁)
            ∘ path→iso (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ)) .from
        ≡⟨ ap (λ u → (u ∘ plugh₁) ∘ path→iso (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ)) .from)
              subst₁ ⟩
          (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁)
            ∘ ⌜ path→iso (ap ⊗-context (interchangeₘ-boundary Θ Γ Μ Δ Κ)) .from ⌝
        ≡⟨ ap! (ap (λ i → i .from) (ic-boundary-chain Θ Γ Μ Δ Κ .char)) ⟩
          (((f ∘ plugg) ∘ slot₁-iso .from) ∘ plugh₁) ∘ bdry-iso .from
        ≡⟨ sym (assoc _ _ _) ∙ sym (assoc _ _ _) ∙ sym (assoc _ _ _) ⟩
          f ∘ ⌜ plugg ∘ slot₁-iso .from ∘ plugh₁ ∘ bdry-iso .from ⌝
        ≡⟨ ap! ic-plug-coherence ⟩
          f ∘ rest₂
        ≡⟨ sym RHS-red ⟩
          subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₂ Θ x Μ Δ Κ)
            (subst (λ Ω → Hom (⊗-context Ω) z) (interchange-slot₀ Θ x Μ y Κ) f ∘ plugh₂) ∘ plugg₂
        ∎

  -- ==========================================================================
  -- Representability: every context Γ is represented by (⊗-context Γ, id).
  -- Plugging the categorical identity into Γ's slot is an isomorphism (Piso Θ),
  -- so precomposition with it is an equivalence — which is exactly the
  -- universality of `id : Homₘ Γ (⊗-context Γ)`.
  -- ==========================================================================

  -- plug Θ Γ Ξ id, packaged as an iso, by induction on the prefix Θ.
  Piso : (Θ Γ Ξ : List Ob)
    → ⊗-context (Θ ++ Γ ++ Ξ) ≅ ⊗-context (Θ ++ ⊗-context Γ ∷ Ξ)
  Piso []      Γ Ξ = ⊗-context-++ Γ Ξ
  Piso (a ∷ Θ) Γ Ξ = ▶.F-map-iso (Piso Θ Γ Ξ)

  -- plug Θ Γ Ξ id ≡ Piso Θ Γ Ξ .to (base: plug-nil + id-whiskering; step:
  -- plug-cons + ▶ on the IH).
  plug-id : (Θ Γ Ξ : List Ob) → plug Θ Γ Ξ id ≡ Piso Θ Γ Ξ .to
  plug-id []      Γ Ξ =
      plug-nil Γ Ξ id
    ∙ ap (_∘ (⊗-context-++ Γ Ξ) .to) (◀.F-id {A = ⊗-context Ξ})
    ∙ idl _
  plug-id (a ∷ Θ) Γ Ξ =
      plug-cons a Θ Γ Ξ id
    ∙ ap (a ▶_) (plug-id Θ Γ Ξ)

  -- Universality of id: f ↦ f ∘ₘ id = f ∘ plug Θ Γ Ξ id = f ∘ Piso.to is
  -- precomposition with an iso, hence an equivalence.
  is-universal-id : (Γ : List Ob)
    → Rep.is-universal Mc {Γ = Γ} {t = ⊗-context Γ} id
  is-universal-id Γ {Θ} {Ξ} {z} = P
    where
      -- The explicit `_∘ₘ_ {Θ}{Ξ}` annotation pins the otherwise-ambiguous
      -- list-append unification (Θ ++ ⊗Γ ∷ Ξ) of the plug's prefix.
      P : is-equiv (λ (f : Mc .Homₘ (Θ ++ ⊗-context Γ ∷ Ξ) z)
                      → Mc ._∘ₘ_ {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {x = ⊗-context Γ} f id)
      P = subst (λ g → is-equiv (λ f → f ∘ g)) (sym (plug-id Θ Γ Ξ))
            (invertible-precomp-equiv (iso→invertible (Piso Θ Γ Ξ)))

  Mc-repr : Rep.is-representable Mc
  Mc-repr Γ = ⊗-context Γ , id {⊗-context Γ}
            , λ {Θ} {Ξ} {z} → is-universal-id Γ {Θ} {Ξ} {z}

-- Top-level re-exports of the module contents.
monoidal→multicategory
  : ∀ {o h} (C : Precategory o h) → Monoidal-category C → Premulticategory o h
monoidal→multicategory C M = Repr.Mc C M

monoidal→multicategory-is-representable
  : ∀ {o h} (C : Precategory o h) (M : Monoidal-category C)
  → Rep.is-representable (monoidal→multicategory C M)
monoidal→multicategory-is-representable C M = Repr.Mc-repr C M

