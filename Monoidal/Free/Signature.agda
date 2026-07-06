open import 1Lab.Prelude

open import Data.Vec.Base

module Monoidal.Free.Signature where
-- define monoidal signatures
-- types
module types {ℓ} (T : Type ℓ) where
  infixr 20 _`⊗_
  infix 25 `_

  data Ty : Type ℓ where
    `I : Ty
    `_ : T → Ty
    _`⊗_ : Ty → Ty → Ty

open types using (module Ty ; `_ ; _`⊗_ ; `I) public

-- a monoidal signature has base types and operations
record 𝓖 ℓ : Type (lsuc ℓ) where
  field
    Ob : Type ℓ
    Ob-is-set : is-set Ob
    Hom : {n : Nat} → Vec (types.Ty Ob) n → Ob → Type ℓ
    Hom-is-set : {n : Nat} → ∀ {σ τ} → is-set (Hom {n} σ τ)

  open types Ob using (Ty) public
