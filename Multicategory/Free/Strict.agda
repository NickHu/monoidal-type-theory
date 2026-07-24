open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base

open import Multicategory.Free
open import Monoidal.Strict
import Multicategory.Strictification

module Multicategory.Free.Strict {o h} (G : Multigraph o h) where

-- A strict monoidal category obtained by strictifying the free representable
-- multicategory FMonCat G (Shulman's simple type theory, Theorem 2.4.10) via
-- the abstract Hermida strictification.  Objects are contexts (lists of
-- types); the tensor is context concatenation, strictly associative and
-- unital.  Monoidally it plays the role of the free monoidal category on G,
-- but no universal property is proven for it here — and the strict
-- 1-categorical freeness would in fact fail for this object: its objects are
-- all contexts (List Ty), not lists of generators.

open import Multicategory.Free.Multicategory G
open import Multicategory.Free.Representable G

module FS = Multicategory.Strictification FMonCat FMonCat-rep

FreeStrict : Precategory o (o ⊔ h)
FreeStrict = FS.Str

FreeStrict-monoidal : Monoidal-category FreeStrict
FreeStrict-monoidal = FS.Str-monoidal

FreeStrict-is-strict : is-strict-monoidal FreeStrict-monoidal
FreeStrict-is-strict = FS.Str-is-strict
