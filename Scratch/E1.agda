-- Scratch experiment E1: the missing strictness statement.
--
-- Part 0: `path-to`, the morphism underlying `path→iso` of an object path.
-- Part 1: `is-strict-monoidal` — a monoidal category is STRICT when its
--         associator/unitors are transports (`path→iso`) of object-TYPE paths,
--         and those paths themselves satisfy Mac Lane's pentagon and triangle
--         (one homotopy level up).  Path families are automatically
--         homotopy-natural, so pentagon+triangle is the complete axiom set —
--         exactly Mac Lane's — and `set→is-strict-monoidal` shows the two
--         path-coherence fields are free when Ob is a set (the classical case:
--         monoid in strict Cat).
-- Part 2: the Hermida strictification `Str-monoidal` of any representable
--         multicategory IS strict in this sense (α-path = ++-assoc,
--         λ-path = refl, ρ-path = ++-idr; no set-ness of Obₘ needed).
-- Part 3: the headline theorem, fully assembled: every monoidal category is
--         monoidally equivalent to a strict one (strong monoidal comparison
--         functor Str → C that is an equivalence of categories).
module Scratch.E1 where

open import 1Lab.Prelude
open import Cat.Base
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso)
open import Cat.Functor.Equivalence using (is-equivalence)
import Cat.Monoidal.Functor as MonF
import Cat.Morphism
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Instances.Monoidal as IM
import Multicategory.Instances.Monoidal.Coherence as Coh

-- ===========================================================================
-- Part 0: transport of an object path, as a morphism.
-- ===========================================================================

module _ {o ℓ} {C : Precategory o ℓ} where
  private module CM = Cat.Morphism C

  path-to : {A B : Precategory.Ob C} → A ≡ B → Precategory.Hom C A B
  path-to p = CM._≅_.to (path→iso p)

-- ===========================================================================
-- Part 1: the strictness predicate.
-- ===========================================================================

-- A monoidal category is strict when the tensor descends from a (coherent)
-- monoid structure on the object type: associativity/unit PATHS whose
-- transports are the structure isomorphisms, and which satisfy the pentagon
-- and triangle one level up.  When Ob is a set the last two fields are
-- propositions with automatic proofs (see `set→is-strict-monoidal`), so this
-- specialises to the classical notion (a monoid in strict Cat).
record is-strict-monoidal
  {o ℓ} {C : Precategory o ℓ} (M : Monoidal-category C) : Type (o ⊔ ℓ)
  where
  no-eta-equality
  open Precategory C using (Ob)
  open Monoidal-category M using (_⊗_ ; Unit ; α→ ; λ← ; ρ←)

  field
    -- The tensor is associative and unital along object-type paths...
    α-path : (A B C' : Ob) → (A ⊗ B) ⊗ C' ≡ A ⊗ (B ⊗ C')
    λ-path : (A : Ob) → Unit ⊗ A ≡ A
    ρ-path : (A : Ob) → A ⊗ Unit ≡ A

    -- ...the monoidal structure isos are precisely the transports of these
    -- paths (one leg each suffices: inverses are unique)...
    α→-is-path : (A B C' : Ob) → α→ (A , B , C') ≡ path-to {C = C} (α-path A B C')
    λ←-is-path : (A : Ob) → λ← A ≡ path-to {C = C} (λ-path A)
    ρ←-is-path : (A : Ob) → ρ← A ≡ path-to {C = C} (ρ-path A)

    -- ...and the paths are themselves Mac Lane-coherent.  (Naturality is
    -- automatic for path families, so these two axioms are the complete set.)
    path-triangle : (A B : Ob)
      → α-path A Unit B ∙ ap (A ⊗_) (λ-path B) ≡ ap (_⊗ B) (ρ-path A)
    path-pentagon : (A B C' D : Ob)
      → ap (_⊗ D) (α-path A B C') ∙ α-path A (B ⊗ C') D ∙ ap (A ⊗_) (α-path B C' D)
        ≡ α-path (A ⊗ B) C' D ∙ α-path A B (C' ⊗ D)

-- When the object type is a set, the two path-coherence conditions are free:
-- the naive definition ("the isos are transports of paths") and the coherent
-- one agree, recovering the classical notion of strict monoidal category.
module _ {o ℓ} {C : Precategory o ℓ} {M : Monoidal-category C} where
  open Precategory C using (Ob)
  open Monoidal-category M using (_⊗_ ; Unit ; α→ ; λ← ; ρ←)

  set→is-strict-monoidal
    : is-set Ob
    → (αp : (A B C' : Ob) → (A ⊗ B) ⊗ C' ≡ A ⊗ (B ⊗ C'))
    → (λp : (A : Ob) → Unit ⊗ A ≡ A)
    → (ρp : (A : Ob) → A ⊗ Unit ≡ A)
    → ((A B C' : Ob) → α→ (A , B , C') ≡ path-to {C = C} (αp A B C'))
    → ((A : Ob) → λ← A ≡ path-to {C = C} (λp A))
    → ((A : Ob) → ρ← A ≡ path-to {C = C} (ρp A))
    → is-strict-monoidal M
  set→is-strict-monoidal Ob-set αp λp ρp αc λc ρc = record
    { α-path = αp ; λ-path = λp ; ρ-path = ρp
    ; α→-is-path = αc ; λ←-is-path = λc ; ρ←-is-path = ρc
    ; path-triangle = λ A B → Ob-set _ _ _ _
    ; path-pentagon = λ A B C' D → Ob-set _ _ _ _
    }

-- ===========================================================================
-- Part 2: the Hermida strictification is strict.
-- ===========================================================================

module _ {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where
  open Premulticategory M using (Obₘ)
  open Strict M rep using (Str ; Str-monoidal ; ⊗₀ ; ≅to ; ≅to-refl ; ≅from-to)

  private
    module SM = Cat.Morphism Str

    -- Str's own path→iso along a List-level path p is Unary's path→iso along
    -- ap ⊗₀ p (Str.Hom Γ Δ = Unary.Hom (⊗₀ Γ) (⊗₀ Δ)); bridged by J, both ends
    -- landing on the identity at refl.
    str-bridge : {Γ Δ : List Obₘ} (p : Γ ≡ Δ)
               → path-to {C = Str} p ≡ ≅to (ap ⊗₀ p)
    str-bridge {Γ} =
      J (λ Δ p → path-to {C = Str} p ≡ ≅to (ap ⊗₀ p))
        (ap SM._≅_.to (transport-refl SM.id-iso) ∙ sym ≅to-refl)

    -- Spine-level coherences for ++ (private duplicates of Strictification's
    -- private lemmas; the real fix is to export them there).
    ++-assoc-nil : (Γ Ξ : List Obₘ) → ++-assoc Γ [] Ξ ≡ ap (_++ Ξ) (++-idr Γ)
    ++-assoc-nil []      Ξ = refl
    ++-assoc-nil (a ∷ Γ) Ξ = ap (ap (a ∷_)) (++-assoc-nil Γ Ξ)

    -- Mac Lane's pentagon for the ++-associator, in the α→ direction.
    ++-pentagon→ : (A B C D : List Obₘ)
      → ap (_++ D) (++-assoc A B C) ∙ ++-assoc A (B ++ C) D
          ∙ ap (A ++_) (++-assoc B C D)
        ≡ ++-assoc (A ++ B) C D ∙ ++-assoc A B (C ++ D)
    ++-pentagon→ [] B C D =
      ∙-idl _ ∙ ∙-idl _ ∙ sym (∙-idr _)
    ++-pentagon→ (a ∷ A) B C D =
        ap (ap (a ∷_) p₁ ∙_) (sym (ap-∙ (a ∷_) p₂ p₃))
      ∙ sym (ap-∙ (a ∷_) p₁ (p₂ ∙ p₃))
      ∙ ap (ap (a ∷_)) (++-pentagon→ A B C D)
      ∙ ap-∙ (a ∷_) q₁ q₂
      where
        p₁ = ap (_++ D) (++-assoc A B C)
        p₂ = ++-assoc A (B ++ C) D
        p₃ = ap (A ++_) (++-assoc B C D)
        q₁ = ++-assoc (A ++ B) C D
        q₂ = ++-assoc A B (C ++ D)

  -- The strictification carries the strictness structure: the tensor on
  -- objects is ++, whose monoid paths are ++-assoc/refl/++-idr, and
  -- Str-monoidal's associator/unitors are BY CONSTRUCTION the ≅to's of
  -- (ap ⊗₀ of) those paths.  No truncation assumption on Obₘ anywhere.
  Str-is-strict : is-strict-monoidal Str-monoidal
  Str-is-strict .is-strict-monoidal.α-path Γ Δ Ε = ++-assoc Γ Δ Ε
  Str-is-strict .is-strict-monoidal.λ-path Γ     = refl
  Str-is-strict .is-strict-monoidal.ρ-path Γ     = ++-idr Γ
  Str-is-strict .is-strict-monoidal.α→-is-path Γ Δ Ε =
    sym (str-bridge (++-assoc Γ Δ Ε))
  Str-is-strict .is-strict-monoidal.λ←-is-path Γ =
    sym (str-bridge refl ∙ ≅to-refl)
  Str-is-strict .is-strict-monoidal.ρ←-is-path Γ =
    ≅from-to (ap ⊗₀ (sym (++-idr Γ))) ∙ sym (str-bridge (++-idr Γ))
  Str-is-strict .is-strict-monoidal.path-triangle Γ Δ =
    ∙-idr (++-assoc Γ [] Δ) ∙ ++-assoc-nil Γ Δ
  Str-is-strict .is-strict-monoidal.path-pentagon = ++-pentagon→

-- ===========================================================================
-- Part 3: the headline theorem, assembled from existing pieces.
--
-- Every monoidal category is monoidally equivalent to a strict one: there is
-- a strict monoidal category (Str, Str-monoidal) and a strong monoidal
-- functor Str → C whose underlying functor is an equivalence of categories.
-- ===========================================================================

module Headline {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where
  private
    Mᵣ : Premulticategory o h
    Mᵣ = IM.monoidal→multicategory C M₀

    rep : Rep.is-representable Mᵣ
    rep = IM.monoidal→multicategory-is-representable C M₀

    module S = Strict Mᵣ rep
    module K = Coh C M₀

  monoidal-strictification
    : Σ[ Cˢ ∈ Precategory o h ]
      Σ[ Mˢ ∈ Monoidal-category Cˢ ]
      ( is-strict-monoidal Mˢ
      × Σ[ F ∈ Functor Cˢ C ]
        ( MonF.Monoidal-functor-on Mˢ M₀ F
        × is-equivalence F ) )
  monoidal-strictification =
      S.Str
    , S.Str-monoidal
    , Str-is-strict Mᵣ rep
    , K.Comparison
    , K.Comparison-monoidal
    , K.Comparison-is-equivalence
