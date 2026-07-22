open import 1Lab.Prelude
open import Cat.Base
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso)
import Cat.Morphism

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
