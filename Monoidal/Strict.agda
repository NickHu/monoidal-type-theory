open import 1Lab.Prelude hiding (id ; _∘_)
open import 1Lab.Path.Reasoning using (∙-swapl)
open import Cat.Base
open import Cat.Bi.Base using (compose-assocˡ ; compose-assocʳ)
open import Cat.Functor.Bifunctor using (Bifunctor)
import Cat.Functor.Base as FB
open import Cat.Functor.Naturality using (isoⁿ→iso)
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso ; path→to-∙ ; path→to-sym)
import Cat.Morphism
import Cat.Reasoning as Cr

-- Strict monoidal categories.
--
-- Classically, a monoidal category is *strict* when its associator and
-- unitors are identities — equivalently, when it is a monoid in Cat.  In a
-- univalent setting "the associator is the identity" must be phrased along
-- paths of the object type: the tensor descends from a monoid structure on
-- the objects, and the structure isomorphisms are the transports (path→iso)
-- of the monoid's associativity/unit paths.
--
-- On a general object type a bare family of such paths is not yet a monoid
-- structure: it must be coherent, and the mathematically correct amount of
-- coherence for a 1-category is one homotopy level up — Mac Lane's pentagon
-- and triangle, now between PATHS.  Crucially no naturality axioms are
-- needed at the path level (path families are automatically
-- homotopy-natural), so pentagon + triangle really is the complete set.
-- When the object type is a set both coherence fields are propositions with
-- automatic proofs (set→is-strict-monoidal below), recovering the classical
-- notion.
--
-- Note that on a non-set object type this is *structure*, not property —
-- as expected: "equality of functors" is only well-behaved on set-level
-- data, and the classical statement quietly assumes it.
module Monoidal.Strict where

-- The morphism underlying `path→iso` of an object path.
module _ {o ℓ} {C : Precategory o ℓ} where
  private module CM = Cat.Morphism C

  path-to : {A B : Precategory.Ob C} → A ≡ B → Precategory.Hom C A B
  path-to p = CM._≅_.to (path→iso p)

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
    -- paths (pinning one leg of each iso suffices — inverses are unique; the
    -- legs are chosen to run in the same direction as the paths, avoiding
    -- sym noise: α→ : (A⊗B)⊗C → A⊗(B⊗C), λ← : Unit⊗A → A, ρ← : A⊗Unit → A)...
    α→-is-path : (A B C' : Ob) → α→ (A , B , C') ≡ path-to {C = C} (α-path A B C')
    λ←-is-path : (A : Ob) → λ← A ≡ path-to {C = C} (λ-path A)
    ρ←-is-path : (A : Ob) → ρ← A ≡ path-to {C = C} (ρ-path A)

    -- ...and the paths are themselves Mac Lane-coherent, one level up.
    path-triangle : (A B : Ob)
      → α-path A Unit B ∙ ap (A ⊗_) (λ-path B) ≡ ap (_⊗ B) (ρ-path A)
    path-pentagon : (A B C' D : Ob)
      → ap (_⊗ D) (α-path A B C') ∙ α-path A (B ⊗ C') D ∙ ap (A ⊗_) (α-path B C' D)
        ≡ α-path (A ⊗ B) C' D ∙ α-path A B (C' ⊗ D)

-- When the object type is a set the two path-coherence conditions are free:
-- the naive definition ("the structure isos are transports of paths") and
-- the coherent one agree, i.e. this specialises to a monoid in strict Cat.
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
-- The converse constructor: a coherent path-monoid acting naturally induces
-- a (strict) monoidal structure.
--
-- Given the five STRUCTURE fields of a monoidal category — tensor, unit, and
-- the three structural natural isomorphisms, i.e. everything EXCEPT the
-- coherence axioms — together with a coherent path-monoid the components
-- descend from, Mac Lane's triangle and pentagon are derived generically:
-- path→iso is functorial (path→to-∙) and commutes with the two whiskerings
-- (ap-F₀-to-iso), so each axiom is the functorial image of its path-level
-- counterpart.  The naturality of the three isos is the only genuinely
-- categorical input; everything else is object-space algebra.
--
-- The structure fields pass through untouched, so the resulting record's
-- components are definitionally the ones supplied.
-- ===========================================================================
module from-path-monoid
  {o ℓ} {C : Precategory o ℓ}
  (-⊗-  : Bifunctor C C C)
  (Unit : Precategory.Ob C)
  (unitor-l : Cr._≅_ Cat[ C , C ] Id (Bifunctor.Right -⊗- Unit))
  (unitor-r : Cr._≅_ Cat[ C , C ] Id (Bifunctor.Left -⊗- Unit))
  (associator : Cr._≅_ Cat[ C ×ᶜ C ×ᶜ C , C ]
      (compose-assocˡ {O = ⊤} (λ _ _ → C) -⊗-)
      (compose-assocʳ {O = ⊤} (λ _ _ → C) -⊗-))
  where

  open Cr C
  open Bifunctor -⊗- using (_◀_ ; _▶_ ; Left ; Right) renaming (F₀ to _⊗_)
  open Cat.Base._=>_ using (η)

  private
    module UL = Cr._≅_ _ unitor-l
    module UR = Cr._≅_ _ unitor-r
    module AS = Cr._≅_ _ associator

    -- Components of the structure isos, named as in Monoidal-category.
    λ←ᶜ : ∀ A → Hom (Unit ⊗ A) A
    λ←ᶜ A = UL.from .η A

    ρ←ᶜ : ∀ A → Hom (A ⊗ Unit) A
    ρ←ᶜ A = UR.from .η A

    α→ᶜ : ∀ A B C' → Hom ((A ⊗ B) ⊗ C') (A ⊗ (B ⊗ C'))
    α→ᶜ A B C' = AS.to .η (A , B , C')

    α←ᶜ : ∀ A B C' → Hom (A ⊗ (B ⊗ C')) ((A ⊗ B) ⊗ C')
    α←ᶜ A B C' = AS.from .η (A , B , C')

    pto : {A B : Ob} → A ≡ B → Hom A B
    pto = path-to {C = C}

    -- path→iso is functorial, and commutes with the two whiskerings.
    pto-∙ : {A B C' : Ob} (p : A ≡ B) (q : B ≡ C')
          → pto (p ∙ q) ≡ pto q ∘ pto p
    pto-∙ = path→to-∙ C

    pto-▶ : (A : Ob) {X Y : Ob} (p : X ≡ Y)
          → pto (ap (A ⊗_) p) ≡ A ▶ pto p
    pto-▶ A p = ap (λ i → i .to) (R.ap-F₀-to-iso p)
      where module R = FB.F-iso (Right A)

    pto-◀ : (B : Ob) {X Y : Ob} (p : X ≡ Y)
          → pto (ap (_⊗ B) p) ≡ pto p ◀ B
    pto-◀ B p = ap (λ i → i .to) (L.ap-F₀-to-iso p)
      where module L = FB.F-iso (Left B)

    -- If f is the transport of p, any left inverse of f is the transport of
    -- sym p (inverses are unique).
    inv-is-path : {A B : Ob} {f : Hom A B} {g : Hom B A} (p : A ≡ B)
                → f ≡ pto p → g ∘ f ≡ id → g ≡ pto (sym p)
    inv-is-path p e h =
        intror (ap (_∘ path→iso p .from) e ∙ path→iso p .invl)
      ∙ pulll h ∙ idl _
      ∙ path→to-sym C p

  -- The coherent path-monoid the structure descends from.  Field names match
  -- is-strict-monoidal, so the strictness witness is a repackaging.
  record Coherent-path-monoid : Type (o ⊔ ℓ) where
    field
      α-path : (A B C' : Ob) → (A ⊗ B) ⊗ C' ≡ A ⊗ (B ⊗ C')
      λ-path : (A : Ob) → Unit ⊗ A ≡ A
      ρ-path : (A : Ob) → A ⊗ Unit ≡ A

      α→-is-path : (A B C' : Ob) → α→ᶜ A B C' ≡ pto (α-path A B C')
      λ←-is-path : (A : Ob) → λ←ᶜ A ≡ pto (λ-path A)
      ρ←-is-path : (A : Ob) → ρ←ᶜ A ≡ pto (ρ-path A)

      path-triangle : (A B : Ob)
        → α-path A Unit B ∙ ap (A ⊗_) (λ-path B) ≡ ap (_⊗ B) (ρ-path A)
      path-pentagon : (A B C' D : Ob)
        → ap (_⊗ D) (α-path A B C') ∙ α-path A (B ⊗ C') D ∙ ap (A ⊗_) (α-path B C' D)
          ≡ α-path (A ⊗ B) C' D ∙ α-path A B (C' ⊗ D)

  module _ (P : Coherent-path-monoid) where
    open Coherent-path-monoid P

    private
      -- The inverse associator components also descend.
      α←-is-path : ∀ A B C' → α←ᶜ A B C' ≡ pto (sym (α-path A B C'))
      α←-is-path A B C' =
        inv-is-path (α-path A B C') (α→-is-path A B C')
          (isoⁿ→iso associator (A , B , C') .invr)

      -- Mac Lane's triangle, as the image of the path-level triangle.
      triangle' : ∀ {A B} → (ρ←ᶜ A ◀ B) ∘ α←ᶜ A Unit B ≡ A ▶ λ←ᶜ B
      triangle' {A} {B} =
        (ρ←ᶜ A ◀ B) ∘ α←ᶜ A Unit B
          ≡⟨ ap₂ _∘_ (ap (_◀ B) (ρ←-is-path A) ∙ sym (pto-◀ B (ρ-path A)))
                     (α←-is-path A Unit B) ⟩
        pto (ap (_⊗ B) (ρ-path A)) ∘ pto (sym (α-path A Unit B))
          ≡˘⟨ pto-∙ (sym (α-path A Unit B)) (ap (_⊗ B) (ρ-path A)) ⟩
        pto (sym (α-path A Unit B) ∙ ap (_⊗ B) (ρ-path A))
          ≡˘⟨ ap pto (∙-swapl (path-triangle A B)) ⟩
        pto (ap (A ⊗_) (λ-path B))
          ≡⟨ pto-▶ A (λ-path B) ⟩
        A ▶ pto (λ-path B)
          ≡˘⟨ ap (A ▶_) (λ←-is-path B) ⟩
        A ▶ λ←ᶜ B
          ∎

      -- Mac Lane's pentagon, as the image of the path-level pentagon.
      pentagon' : ∀ {A B C' D}
        → (α←ᶜ A B C' ◀ D) ∘ α←ᶜ A (B ⊗ C') D ∘ (A ▶ α←ᶜ B C' D)
        ≡ α←ᶜ (A ⊗ B) C' D ∘ α←ᶜ A B (C' ⊗ D)
      pentagon' {A} {B} {C'} {D} =
        (α←ᶜ A B C' ◀ D) ∘ α←ᶜ A (B ⊗ C') D ∘ (A ▶ α←ᶜ B C' D)
          ≡⟨ ap₂ _∘_ (ap (_◀ D) (α←-is-path A B C') ∙ sym (pto-◀ D (sym p₁)))
               (ap₂ _∘_ (α←-is-path A (B ⊗ C') D)
                  (ap (A ▶_) (α←-is-path B C' D) ∙ sym (pto-▶ A (sym p₃)))) ⟩
        pto (ap (_⊗ D) (sym p₁)) ∘ pto (sym p₂) ∘ pto (ap (A ⊗_) (sym p₃))
          ≡˘⟨ ap (pto (ap (_⊗ D) (sym p₁)) ∘_) (pto-∙ (ap (A ⊗_) (sym p₃)) (sym p₂)) ⟩
        pto (ap (_⊗ D) (sym p₁)) ∘ pto (ap (A ⊗_) (sym p₃) ∙ sym p₂)
          ≡˘⟨ pto-∙ (ap (A ⊗_) (sym p₃) ∙ sym p₂) (ap (_⊗ D) (sym p₁)) ⟩
        pto ((ap (A ⊗_) (sym p₃) ∙ sym p₂) ∙ ap (_⊗ D) (sym p₁))
          ≡⟨ ap pto pcoh ⟩
        pto (sym q₂ ∙ sym q₁)
          ≡⟨ pto-∙ (sym q₂) (sym q₁) ⟩
        pto (sym q₁) ∘ pto (sym q₂)
          ≡˘⟨ ap₂ _∘_ (α←-is-path (A ⊗ B) C' D) (α←-is-path A B (C' ⊗ D)) ⟩
        α←ᶜ (A ⊗ B) C' D ∘ α←ᶜ A B (C' ⊗ D)
          ∎
        where
          p₁ = α-path A B C'
          p₂ = α-path A (B ⊗ C') D
          p₃ = α-path B C' D
          q₁ = α-path (A ⊗ B) C' D
          q₂ = α-path A B (C' ⊗ D)

          -- sym of the path pentagon, with sym pushed through ∙ and ap.
          pcoh : (ap (A ⊗_) (sym p₃) ∙ sym p₂) ∙ ap (_⊗ D) (sym p₁)
               ≡ sym q₂ ∙ sym q₁
          pcoh =
              ap (_∙ ap (_⊗ D) (sym p₁)) (sym (sym-∙ p₂ (ap (A ⊗_) p₃)))
            ∙ sym (sym-∙ (ap (_⊗ D) p₁) (p₂ ∙ ap (A ⊗_) p₃))
            ∙ ap sym (path-pentagon A B C' D)
            ∙ sym-∙ q₁ q₂

    monoidal : Monoidal-category C
    monoidal .Monoidal-category.-⊗- = -⊗-
    monoidal .Monoidal-category.Unit = Unit
    monoidal .Monoidal-category.unitor-l = unitor-l
    monoidal .Monoidal-category.unitor-r = unitor-r
    monoidal .Monoidal-category.associator = associator
    monoidal .Monoidal-category.triangle = triangle'
    monoidal .Monoidal-category.pentagon = pentagon'

    monoidal-is-strict : is-strict-monoidal monoidal
    monoidal-is-strict .is-strict-monoidal.α-path = α-path
    monoidal-is-strict .is-strict-monoidal.λ-path = λ-path
    monoidal-is-strict .is-strict-monoidal.ρ-path = ρ-path
    monoidal-is-strict .is-strict-monoidal.α→-is-path A B C' = α→-is-path A B C'
    monoidal-is-strict .is-strict-monoidal.λ←-is-path = λ←-is-path
    monoidal-is-strict .is-strict-monoidal.ρ←-is-path = ρ←-is-path
    monoidal-is-strict .is-strict-monoidal.path-triangle = path-triangle
    monoidal-is-strict .is-strict-monoidal.path-pentagon = path-pentagon
