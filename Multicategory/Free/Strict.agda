open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open import Cat.Monoidal.Base

open import Multicategory
open import Multicategory.Free
open import Monoidal.Strict
import Multicategory.Strictification

module Multicategory.Free.Strict {o h} (G : Multigraph o h) where

-- The free STRICT monoidal category on a multigraph: Shulman's simple type
-- theory for monoidal categories (the free representable multicategory
-- FMonCat G, Theorem 2.4.10) fed through the abstract Hermida
-- strictification.  Objects are contexts (lists of types); the tensor is
-- context concatenation, strictly associative and unital.

open import Multicategory.Free.Multicategory G
open import Multicategory.Free.Representable G

module FS = Multicategory.Strictification FMonCat FMonCat-rep

FreeStrict : Precategory o (o ⊔ h)
FreeStrict = FS.Str

FreeStrict-monoidal : Monoidal-category FreeStrict
FreeStrict-monoidal = FS.Str-monoidal

FreeStrict-is-strict : is-strict-monoidal FreeStrict-monoidal
FreeStrict-is-strict = FS.Str-is-strict
