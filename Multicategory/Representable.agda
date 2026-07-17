open import Multicategory

open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso; Hom-transport)
import Cat.Functor.Base as FB
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
      -- Transport the domain from ⊗(Γ++[]) to ⊗Γ via the ++-idr boundary.
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
        ≡⟨ {!!} ⟩
          f
        ∎
  Mc .assocₘ f g h    = {!!}
  Mc .interchangeₘ f g h = {!!}
