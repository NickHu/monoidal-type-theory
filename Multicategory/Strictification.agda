open import 1Lab.Prelude
open import Cat.Base
open import Cat.Instances.Product
open import Cat.Functor.Closed using (Curry)
open import Cat.Functor.Bifunctor using (Bifunctor)
import Cat.Functor.Base as FB
open import Cat.Functor.Naturality
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso; path→to-sym; Hom-pathp-refll; Hom-pathp-reflr)
open import 1Lab.Path.Reasoning using (∙-swapl)
import Cat.Morphism
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import ListPath.Solver using (list!)
open import Multicategory.Unary
open import Monoidal.Strict
import Multicategory.Representable as Rep

-- The strict monoidal category arising from a representable multicategory
-- (Hermida).  Objects are lists of objects, the tensor is concatenation, and
-- the underlying category is `Unary M` reindexed along the tensor `⊗`.
module Multicategory.Strictification
  {o h} (M : Premulticategory o h) (rep : Rep.is-representable M) where

  open Premulticategory M
  private module U = Precategory (Unary M)

  -- The tensor of a context and its universal arrow.
  ⊗₀ : List Obₘ → Obₘ
  ⊗₀ = Rep.⊗ M rep

  ⊗-arr : (Γ : List Obₘ) → Homₘ Γ (⊗₀ Γ)
  ⊗-arr = Rep.⊗-arr M rep

  ⊗-arr-univ : (Γ : List Obₘ) → Rep.is-universal M (⊗-arr Γ)
  ⊗-arr-univ = Rep.⊗-arr-universal M rep

  -- The underlying category of the strictification: `Unary M` reindexed along
  -- ⊗.  Morphisms Γ → Δ are unary maps ⊗Γ → ⊗Δ; identities and composition,
  -- and hence the category laws, are inherited from `Unary M`.
  Str : Precategory o h
  Str .Precategory.Ob          = List Obₘ
  Str .Precategory.Hom Γ Δ     = U.Hom (⊗₀ Γ) (⊗₀ Δ)
  Str .Precategory.Hom-set _ _ = U.Hom-set _ _
  Str .Precategory.id          = U.id
  Str .Precategory._∘_         = U._∘_
  Str .Precategory.idr         = U.idr
  Str .Precategory.idl         = U.idl
  Str .Precategory.assoc       = U.assoc

  -- The reindexing made into a functor: identity on hom-sets, ⊗ on objects.
  -- (Multicategory.Strictification.Equivalence shows it is an equivalence.)
  Reindex : Functor Str (Unary M)
  Reindex .Functor.F₀      = ⊗₀
  Reindex .Functor.F₁ f    = f
  Reindex .Functor.F-id    = refl
  Reindex .Functor.F-∘ f g = refl

  -- Structural list-path coherences.  Every list-path reconciliation the
  -- strictification needs is between two paths built ONLY from ++-assoc/++-idr
  -- (refl on elements); they are equal by induction on the spine, for ANY
  -- element type — so `is-set Obₘ` is not needed anywhere below.
  -- (++-assoc-nil, the ++-idr reindex of ++-assoc's empty-middle case, is
  -- imported from Multicategory.)
  private
    -- Naturality of ++-idr against the constant tail [].
    ++-idr-nat : (Γ : List Obₘ) → ap (_++ []) (++-idr Γ) ≡ ++-idr (Γ ++ [])
    ++-idr-nat Γ = list!

    -- interchange-flatten with empty first/third slots is a ++-idr reindex.
    flatten-nil-mid : (Γ Ε : List Obₘ)
                    → interchange-flatten Γ [] Ε [] ≡ ap (_++ (Ε ++ [])) (++-idr Γ)
    flatten-nil-mid []      Ε = refl
    flatten-nil-mid (a ∷ Γ) Ε = ap (ap (a ∷_)) (flatten-nil-mid Γ Ε)

    -- assocₘ-flatten with empty right slots collapses to sym ++-idr.
    assocₘ-flatten-nils : (Γ Δ : List Obₘ)
                        → assocₘ-flatten Γ Δ [] [] ≡ sym (++-idr (Γ ++ (Δ ++ [])))
    assocₘ-flatten-nils []      Δ = ap sym (++-assoc-nil Δ [] ∙ ++-idr-nat Δ)
    assocₘ-flatten-nils (a ∷ Γ) Δ = ap (ap (a ∷_)) (assocₘ-flatten-nils Γ Δ)

    -- ++-idr conjugated by an arbitrary list-path: homotopy-naturality of
    -- ++-idr (as a homotopy _++ [] ∼ id), inverted and reassociated.
    idr-assoc-coh : {V W : List Obₘ} (a : V ≡ W)
                  → (a ∙ sym (++-idr W)) ∙ sym (ap (_++ []) a) ≡ sym (++-idr V)
    idr-assoc-coh {V} {W} a =
        sym (∙-assoc a (sym (++-idr W)) (sym (ap (_++ []) a)))
      ∙ sym (∙-swapl {p = sym a} {q = sym (++-idr V)}
               ( sym (sym-∙ (++-idr V) a)
               ∙ ap sym (homotopy-natural ++-idr a)
               ∙ sym-∙ (ap (_++ []) a) (++-idr W) ))

    -- Mac Lane's pentagon for the ++-associator, at the spine level (α→
    -- direction; the α← direction needed by Monoidal-category's pentagon
    -- field is produced generically by from-path-monoid).
    ++-pentagon→ : (A B C D : List Obₘ)
      → ap (_++ D) (++-assoc A B C) ∙ ++-assoc A (B ++ C) D
          ∙ ap (A ++_) (++-assoc B C D)
        ≡ ++-assoc (A ++ B) C D ∙ ++-assoc A B (C ++ D)
    ++-pentagon→ A B C D = list!

    -- Spine reconciliation for splitμ: the composite of its segment paths
    -- (Ε-pull, Δ-pull, μ-collapse, final ++-idr) against ap (Δ ++_) (++-idr Ε).
    splitμ-coh : (Δ Ε : List Obₘ)
      → ((ap (Δ ++_) (sym (++-assoc Ε [] [])) ∙ sym (++-assoc Δ (Ε ++ []) []))
          ∙ ap (_++ []) (ap (Δ ++_) (++-idr Ε))) ∙ ++-idr (Δ ++ Ε)
        ≡ ap (Δ ++_) (++-idr Ε)
    splitμ-coh [] Ε =
        ap (λ t → (t ∙ ap (_++ []) (++-idr Ε)) ∙ ++-idr Ε)
           (∙-idr (sym (++-assoc Ε [] [])) ∙ ap sym (++-assoc-nil Ε []))
      ∙ ap (_∙ ++-idr Ε) (∙-invl (ap (_++ []) (++-idr Ε)))
      ∙ ∙-idl (++-idr Ε)
    splitμ-coh (a ∷ Δ) Ε =
        ap (λ t → (t ∙ ap (_++ []) (ap ((a ∷ Δ) ++_) (++-idr Ε))) ∙ ++-idr ((a ∷ Δ) ++ Ε))
           (sym (ap-∙ (a ∷_) l₁ l₂))
      ∙ ap (_∙ ++-idr ((a ∷ Δ) ++ Ε)) (sym (ap-∙ (a ∷_) (l₁ ∙ l₂) l₃))
      ∙ sym (ap-∙ (a ∷_) ((l₁ ∙ l₂) ∙ l₃) (++-idr (Δ ++ Ε)))
      ∙ ap (ap (a ∷_)) (splitμ-coh Δ Ε)
      where
        l₁ = ap (Δ ++_) (sym (++-assoc Ε [] []))
        l₂ = sym (++-assoc Δ (Ε ++ []) [])
        l₃ = ap (_++ []) (ap (Δ ++_) (++-idr Ε))

    -- Spine reconciliation for splitμ-l (Δ-pull, Γ-pull, μ-collapse, final
    -- ++-idr) against ++-assoc's spine.
    splitμ-l-coh : (Γ Δ Ε : List Obₘ)
      → ((( ap (Γ ++_) (sym (++-assoc Δ [] (Ε ++ [])))
            ∙ sym (++-assoc Γ (Δ ++ []) (Ε ++ [])) )
          ∙ ap (_++ (Ε ++ [])) (ap (Γ ++_) (++-idr Δ)))
          ∙ ap ((Γ ++ Δ) ++_) (++-idr Ε)) ∙ ++-assoc Γ Δ Ε
        ≡ ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))
    splitμ-l-coh [] Δ Ε =
        ∙-idr (((sym (++-assoc Δ [] (Ε ++ [])) ∙ refl)
                 ∙ ap (_++ (Ε ++ [])) (++-idr Δ)) ∙ ap (Δ ++_) (++-idr Ε))
      ∙ ap (_∙ ap (Δ ++_) (++-idr Ε))
           ( ap (_∙ ap (_++ (Ε ++ [])) (++-idr Δ))
                ( ∙-idr (sym (++-assoc Δ [] (Ε ++ [])))
                ∙ ap sym (++-assoc-nil Δ (Ε ++ [])) )
           ∙ ∙-invl (ap (_++ (Ε ++ [])) (++-idr Δ)) )
      ∙ ∙-idl (ap (Δ ++_) (++-idr Ε))
    splitμ-l-coh (a ∷ Γ) Δ Ε =
        ap (λ t → ((t ∙ l₃') ∙ l₄') ∙ l₅') (sym (ap-∙ (a ∷_) l₁ l₂))
      ∙ ap (λ t → (t ∙ l₄') ∙ l₅') (sym (ap-∙ (a ∷_) (l₁ ∙ l₂) l₃))
      ∙ ap (_∙ l₅') (sym (ap-∙ (a ∷_) ((l₁ ∙ l₂) ∙ l₃) l₄))
      ∙ sym (ap-∙ (a ∷_) (((l₁ ∙ l₂) ∙ l₃) ∙ l₄) (++-assoc Γ Δ Ε))
      ∙ ap (ap (a ∷_)) (splitμ-l-coh Γ Δ Ε)
      where
        l₁ = ap (Γ ++_) (sym (++-assoc Δ [] (Ε ++ [])))
        l₂ = sym (++-assoc Γ (Δ ++ []) (Ε ++ []))
        l₃ = ap (_++ (Ε ++ [])) (ap (Γ ++_) (++-idr Δ))
        l₄ = ap ((Γ ++ Δ) ++_) (++-idr Ε)
        l₃' = ap (_++ (Ε ++ [])) (ap ((a ∷ Γ) ++_) (++-idr Δ))
        l₄' = ap (((a ∷ Γ) ++ Δ) ++_) (++-idr Ε)
        l₅' = ++-assoc (a ∷ Γ) Δ Ε

  -- ======================= PathP kit =======================
  --
  -- The transport-heavy proofs below stay in PathP land: each algebraic move
  -- (an instance of assocₘ or interchangeₘ, or a plug of an arrow along an
  -- earlier move) is a PathP over its list-path, the moves are composed with
  -- ◁ / ▷ / ∙P, and the composite base path is reconciled against the
  -- canonical list-path ONCE at the end (hom-over).  Arrows are plugged into
  -- each segment BEFORE segments are ∙P-composed: a ∙-composite list-path is
  -- an hcomp, not cons-headed, so ∘ₘ-pathp could not see the slot afterwards.

  -- Heterogeneous congruence for _∘ₘ_: free, since _∘ₘ_ is polymorphic in all
  -- three context indices — just apply it under the interval.
  ∘ₘ-pathp : {Θ Θ' Ξ Ξ' Γ Γ' : List Obₘ} {x z : Obₘ}
             (P : Θ ≡ Θ') (Q : Ξ ≡ Ξ') (G : Γ ≡ Γ')
             {f : Homₘ (Θ ++ x ∷ Ξ) z} {f' : Homₘ (Θ' ++ x ∷ Ξ') z}
             {g : Homₘ Γ x} {g' : Homₘ Γ' x}
           → PathP (λ i → Homₘ (P i ++ x ∷ Q i) z) f f'
           → PathP (λ i → Homₘ (G i) x) g g'
           → PathP (λ i → Homₘ (P i ++ G i ++ Q i) z) (f ∘ₘ g) (f' ∘ₘ g')
  ∘ₘ-pathp P Q G ff gg i = _∘ₘ_ {Θ = P i} {Ξ = Q i} (ff i) (gg i)

  -- Reconcile the base path of a PathP of homs along an equality of list-paths.
  hom-over : {Γ Γ' : List Obₘ} {z : Obₘ} {p q : Γ ≡ Γ'} (α : p ≡ q)
             {f : Homₘ Γ z} {g : Homₘ Γ' z}
           → PathP (λ i → Homₘ (p i) z) f g → PathP (λ i → Homₘ (q i) z) f g
  hom-over {z = z} α {f} {g} = subst (λ r → PathP (λ i → Homₘ (r i) z) f g) α

  -- Binary interchange: for χ : Homₘ (x ∷ y ∷ []) z the two plug orders agree
  -- HOMOGENEOUSLY in Homₘ (Γ ++ Δ ++ []) z.  All of interchangeₘ's slot substs
  -- and its boundary transport are absorbed here, once: the slot₁ subst is a
  -- transport-filler over sym (++-idr Γ) (via ++-assoc-nil), and the composite
  -- of that base path with the interchange boundary is a loop that
  -- flatten-nil-mid cancels to refl.
  ic₂ : {x y z : Obₘ} {Γ Δ : List Obₘ}
        (χ : Homₘ (x ∷ y ∷ []) z) (g : Homₘ Γ x) (h : Homₘ Δ y)
      → _∘ₘ_ {Θ = Γ} {Ξ = []} (_∘ₘ_ {Θ = []} {Ξ = y ∷ []} χ g) h
        ≡ _∘ₘ_ {Θ = []} {Ξ = Δ ++ []} (_∘ₘ_ {Θ = x ∷ []} {Ξ = []} χ h) g
  ic₂ {x} {y} {z} {Γ} {Δ} χ g h =
      hom-over loop-refl
        (_∙P_ {B = λ Ω → Homₘ Ω z}
           {p = ap (_++ Δ ++ []) (sym (++-idr Γ))}
           {q = interchange-flatten Γ [] Δ []}
           leg
           (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Γ} {Δ = Δ} χ g h))
    ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Δ ++ []} q g)
         ( transport-refl _
         ∙ ap (λ q → _∘ₘ_ {Θ = x ∷ []} {Ξ = []} q h) (transport-refl χ) )
    where
      BΩ : List Obₘ → Type _
      BΩ Ω = Homₘ Ω z
      S₁ : Γ ++ y ∷ [] ≡ (Γ ++ []) ++ y ∷ []
      S₁ = interchange-slot₁ [] Γ [] y []
      χg : Homₘ (Γ ++ y ∷ []) z
      χg = _∘ₘ_ {Θ = []} {Ξ = y ∷ []} χ g
      slotP : PathP (λ i → Homₘ (sym (++-idr Γ) i ++ y ∷ []) z)
                χg (subst BΩ S₁ χg)
      slotP = hom-over (ap sym (++-assoc-nil Γ (y ∷ [])))
                (transport-filler (λ i → BΩ (S₁ i)) χg)
      leg : PathP (λ i → Homₘ (sym (++-idr Γ) i ++ Δ ++ []) z)
              (_∘ₘ_ {Θ = Γ} {Ξ = []} χg h)
              (_∘ₘ_ {Θ = Γ ++ []} {Ξ = []} (subst BΩ S₁ χg) h)
      leg = ∘ₘ-pathp (sym (++-idr Γ)) refl refl slotP refl
      loop-refl : (ap (_++ Δ ++ []) (sym (++-idr Γ)) ∙ interchange-flatten Γ [] Δ [])
                ≡ refl
      loop-refl =
          ap (ap (_++ Δ ++ []) (sym (++-idr Γ)) ∙_) (flatten-nil-mid Γ Δ)
        ∙ sym (ap-∙ (_++ Δ ++ []) (sym (++-idr Γ)) (++-idr Γ))
        ∙ ap (ap (_++ Δ ++ [])) (∙-invl (++-idr Γ))

  -- assocₘ with the slot-unbury transport absorbed.  When both prefixes Θ, Φ
  -- are CONCRETE cons-lists, slot-unbury Θ Φ y Ψ Ξ is definitionally refl and
  -- its subst is a bare transport-refl; these wrappers cancel it.  The
  -- subscripts record the prefix lengths (|Θ| |Φ|); the five shapes below are
  -- the only ones the file needs.  (When the plugged context Ρ is also
  -- concrete, the assocₘ-boundary is definitionally refl too and the wrapper
  -- is a homogeneous equation.)
  assoc₀₀ : {Ξ Ψ Ρ : List Obₘ} {x y z : Obₘ}
            (f : Homₘ (x ∷ Ξ) z) (g : Homₘ (y ∷ Ψ) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary [] [] Ρ Ψ Ξ i) z)
              (_∘ₘ_ {Θ = []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g) h)
              (_∘ₘ_ {Θ = []} {Ξ = Ξ} f (_∘ₘ_ {Θ = []} {Ξ = Ψ} g h))
  assoc₀₀ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Ψ ++ Ξ} q h)
       (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g)))
      ◁ assocₘ {Θ = []} {Ξ = Ξ} {Φ = []} f g h

  assoc₁₀ : {Ξ Ψ Ρ : List Obₘ} {w x y z : Obₘ}
            (f : Homₘ (w ∷ x ∷ Ξ) z) (g : Homₘ (y ∷ Ψ) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary (w ∷ []) [] Ρ Ψ Ξ i) z)
              (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f g) h)
              (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f (_∘ₘ_ {Θ = []} {Ξ = Ψ} g h))
  assoc₁₀ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = _ ∷ []} {Ξ = Ψ ++ Ξ} q h)
       (sym (transport-refl (_∘ₘ_ {Θ = _ ∷ []} {Ξ = Ξ} f g)))
      ◁ assocₘ {Θ = _ ∷ []} {Ξ = Ξ} {Φ = []} f g h

  assoc₁₁ : {Ξ Ψ Ρ : List Obₘ} {w v x y z : Obₘ}
            (f : Homₘ (w ∷ x ∷ Ξ) z) (g : Homₘ (v ∷ y ∷ Ψ) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary (w ∷ []) (v ∷ []) Ρ Ψ Ξ i) z)
              (_∘ₘ_ {Θ = w ∷ v ∷ []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f g) h)
              (_∘ₘ_ {Θ = w ∷ []} {Ξ = Ξ} f (_∘ₘ_ {Θ = v ∷ []} {Ξ = Ψ} g h))
  assoc₁₁ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = _ ∷ _ ∷ []} {Ξ = Ψ ++ Ξ} q h)
       (sym (transport-refl (_∘ₘ_ {Θ = _ ∷ []} {Ξ = Ξ} f g)))
      ◁ assocₘ {Θ = _ ∷ []} {Ξ = Ξ} {Φ = _ ∷ []} f g h

  assoc₀₁ : {Ξ Ψ Ρ : List Obₘ} {v x y z : Obₘ}
            (f : Homₘ (x ∷ Ξ) z) (g : Homₘ (v ∷ y ∷ Ψ) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary [] (v ∷ []) Ρ Ψ Ξ i) z)
              (_∘ₘ_ {Θ = v ∷ []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g) h)
              (_∘ₘ_ {Θ = []} {Ξ = Ξ} f (_∘ₘ_ {Θ = v ∷ []} {Ξ = Ψ} g h))
  assoc₀₁ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = _ ∷ []} {Ξ = Ψ ++ Ξ} q h)
       (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g)))
      ◁ assocₘ {Θ = []} {Ξ = Ξ} {Φ = _ ∷ []} f g h

  assoc₀₂ : {Ξ Ψ Ρ : List Obₘ} {v w x y z : Obₘ}
            (f : Homₘ (x ∷ Ξ) z) (g : Homₘ (v ∷ w ∷ y ∷ Ψ) x) (h : Homₘ Ρ y)
          → PathP (λ i → Homₘ (assocₘ-boundary [] (v ∷ w ∷ []) Ρ Ψ Ξ i) z)
              (_∘ₘ_ {Θ = v ∷ w ∷ []} {Ξ = Ψ ++ Ξ} (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g) h)
              (_∘ₘ_ {Θ = []} {Ξ = Ξ} f (_∘ₘ_ {Θ = v ∷ w ∷ []} {Ξ = Ψ} g h))
  assoc₀₂ {Ξ} {Ψ} f g h =
    ap (λ q → _∘ₘ_ {Θ = _ ∷ _ ∷ []} {Ξ = Ψ ++ Ξ} q h)
       (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = Ξ} f g)))
      ◁ assocₘ {Θ = []} {Ξ = Ξ} {Φ = _ ∷ _ ∷ []} f g h

  -- Universality, packaged as an equivalence between unary maps out of ⊗Γ and
  -- multimaps out of the context Γ: Representable's `restrE` at the universal
  -- arrow of Γ.  `restrict.injective` is the workhorse: to prove two unary maps
  -- ⊗Γ → z equal, it suffices to compare them after restricting to the
  -- generators Γ.
  module _ {Γ : List Obₘ} {z : Obₘ} where
    restrict-equiv : Homₘ (⊗₀ Γ ∷ []) z ≃ Homₘ Γ z
    restrict-equiv = Rep.restrE M (⊗-arr Γ) (⊗-arr-univ Γ)

    module restrict = Equiv restrict-equiv

  -- restrict φ = φ ∘ₘ ⊗-arr Γ  (up to ++-idr);  expand = its inverse.
  restrict : {Γ : List Obₘ} {z : Obₘ} → Homₘ (⊗₀ Γ ∷ []) z → Homₘ Γ z
  restrict = restrict.to

  expand : {Γ : List Obₘ} {z : Obₘ} → Homₘ Γ z → Homₘ (⊗₀ Γ ∷ []) z
  expand = restrict.from

  -- Two-slot version: restrict both ⊗Γ and ⊗Δ to their generators.  One
  -- ++-idr transport survives (the trailing block Δ ++ []).
  module _ {Γ Δ : List Obₘ} {z : Obₘ} where
    restrict₂-equiv : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) z ≃ Homₘ (Γ ++ Δ) z
    restrict₂-equiv =
        ( (λ (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) z) → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} χ (⊗-arr Γ))
          , ⊗-arr-univ Γ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} )
      ∙e ( (λ (ψ : Homₘ (Γ ++ ⊗₀ Δ ∷ []) z) → _∘ₘ_ {Θ = Γ} {Ξ = []} ψ (⊗-arr Δ))
          , ⊗-arr-univ Δ {Θ = Γ} {Ξ = []} )
      ∙e path→equiv (ap (λ Ω → Homₘ Ω z) (ap (Γ ++_) (++-idr Δ)))

    module restrict₂ = Equiv restrict₂-equiv

  -- Three-slot version: plug ⊗-arr Ε, Δ, Γ in that order — the contexts land on
  -- Γ ++ (Δ ++ Ε) with NO reassoc transport.
  module _ {Γ Δ Ε : List Obₘ} {z : Obₘ} where
    restrict₃-equiv : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z ≃ Homₘ (Γ ++ (Δ ++ Ε)) z
    restrict₃-equiv =
        ( (λ (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z)
             → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} χ (⊗-arr Ε))
          , ⊗-arr-univ Ε {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} )
      ∙e ( (λ (ψ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ (Ε ++ [])) z)
             → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} ψ (⊗-arr Δ))
          , ⊗-arr-univ Δ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} )
      ∙e ( (λ (φ : Homₘ (⊗₀ Γ ∷ (Δ ++ (Ε ++ []))) z)
             → _∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])} φ (⊗-arr Γ))
          , ⊗-arr-univ Γ {Θ = []} {Ξ = Δ ++ (Ε ++ [])} )
      ∙e path→equiv (ap (λ Ω → Homₘ Ω z) (ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))))

    module restrict₃ = Equiv restrict₃-equiv

  -- The comparison map μ : ⊗Γ ⊗ ⊗Δ → ⊗(Γ ++ Δ), obtained as the unique unary
  -- map that restricts to the universal arrow of Γ ++ Δ.
  μ : (Γ Δ : List Obₘ) → Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ ++ Δ))
  μ Γ Δ = restrict₂.from (⊗-arr (Γ ++ Δ))

  -- The tensor of two morphisms: combine f, g through μ and re-express as a
  -- unary map out of ⊗(Γ ++ Δ).
  _⊗ₛ_ : {Γ Γ' Δ Δ' : List Obₘ}
       → U.Hom (⊗₀ Γ) (⊗₀ Γ') → U.Hom (⊗₀ Δ) (⊗₀ Δ')
       → U.Hom (⊗₀ (Γ ++ Δ)) (⊗₀ (Γ' ++ Δ'))
  _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g =
    expand (restrict₂.to
      (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
        (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f) g))

  -- restricting the unary identity recovers the universal arrow.
  restrict-id : (Γ : List Obₘ) → restrict (U.id {⊗₀ Γ}) ≡ ⊗-arr Γ
  restrict-id Γ = from-pathp (idₘr (⊗-arr Γ))

  -- μ restricts to the universal arrow of Γ ++ Δ (definition of μ).
  restrict₂-μ : (Γ Δ : List Obₘ) → restrict₂.to (μ Γ Δ) ≡ ⊗-arr (Γ ++ Δ)
  restrict₂-μ Γ Δ = restrict₂.ε (⊗-arr (Γ ++ Δ))

  -- Bifunctoriality: the tensor preserves identities.
  ⊗ₛ-id : (Γ Δ : List Obₘ) → _⊗ₛ_ {Γ} {Γ} {Δ} {Δ} U.id U.id ≡ U.id
  ⊗ₛ-id Γ Δ = restrict.injective (
    restrict (_⊗ₛ_ {Γ} {Γ} {Δ} {Δ} U.id U.id)              ≡⟨ restrict.ε _ ⟩
    restrict₂.to (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
      (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (μ Γ Δ) idₘ) idₘ)     ≡⟨ ap restrict₂.to collapse-ids ⟩
    restrict₂.to (μ Γ Δ)                                    ≡⟨ restrict₂-μ Γ Δ ⟩
    ⊗-arr (Γ ++ Δ)                                         ≡˘⟨ restrict-id (Γ ++ Δ) ⟩
    restrict (U.id {⊗₀ (Γ ++ Δ)})                          ∎)
    where
      collapse-ids : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (μ Γ Δ) idₘ) idₘ ≡ μ Γ Δ
      collapse-ids = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q idₘ)
                 (idₘl {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (μ Γ Δ))
            ∙ idₘl {Θ = ⊗₀ Γ ∷ []} {Ξ = []} (μ Γ Δ)

  -- `restrict` is natural under unary post-composition: Representable's
  -- plug-nat at the universal arrow.
  restrict-nat : {Γ : List Obₘ} {w z : Obₘ}
                 (a : Homₘ (w ∷ []) z) (φ : Homₘ (⊗₀ Γ ∷ []) w)
               → restrict {Γ} {z} (a U.∘ φ)
                 ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
                     (_∘ₘ_ {Θ = []} {Ξ = []} a (restrict {Γ} {w} φ))
  restrict-nat {Γ} = Rep.plug-nat M (⊗-arr Γ)

  -- Pull `a` past the first universal arrow (front slot, suffix ⊗Δ∷[]): the
  -- assocₘ boundary at these prefixes is exactly ++-assoc Γ (⊗Δ∷[]) [].
  eqΓ : {Γ Δ : List Obₘ} {w z : Obₘ}
        (a : Homₘ (w ∷ []) z) (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) w)
      → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} a χ) (⊗-arr Γ)
        ≡ subst (λ Ω → Homₘ Ω z) (++-assoc Γ (⊗₀ Δ ∷ []) [])
            (_∘ₘ_ {Θ = []} {Ξ = []} a (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} χ (⊗-arr Γ)))
  eqΓ {Γ} a χ = from-pathp⁻ (assoc₀₀ a χ (⊗-arr Γ))

  -- Naturality of the two-slot restriction under unary post-composition.  eqΓ
  -- pulls `a` past ⊗-arr Γ; its subst is exactly the slot-unbury of a second
  -- assocₘ, which then pulls `a` past ⊗-arr Δ.  The residual list-path loop is
  -- reconciled by the spine lemma assocₘ-flatten-nils + naturality of ++-idr
  -- (no truncation of Obₘ anywhere).
  restrict₂-nat : {Γ Δ : List Obₘ} {w z : Obₘ}
                  (a : Homₘ (w ∷ []) z) (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) w)
                → restrict₂.to {Γ} {Δ} (_∘ₘ_ {Θ = []} {Ξ = []} a χ)
                  ≡ subst (λ Ω → Homₘ Ω z) (++-idr (Γ ++ Δ))
                      (_∘ₘ_ {Θ = []} {Ξ = []} a (restrict₂.to {Γ} {Δ} χ))
  restrict₂-nat {Γ} {Δ} {w} {z} a χ =
      ap (subst (λ Ω → Homₘ Ω z) P) front-assoc
    ∙ sym (subst-∙ (λ Ω → Homₘ Ω z) (sym bd2) P as2)
    ∙ ap (λ p → subst (λ Ω → Homₘ Ω z) p as2)
         (ap (_∙ P) (ap sym (assocₘ-flatten-nils Γ Δ)) ∙ homotopy-natural ++-idr P)
    ∙ subst-∙ (λ Ω → Homₘ Ω z) (ap (_++ []) P) (++-idr (Γ ++ Δ)) as2
    ∙ sym (ap (subst (λ Ω → Homₘ Ω z) (++-idr (Γ ++ Δ))) (Rep.∘ₘ-substr M a P s2))
    where
      P : Γ ++ (Δ ++ []) ≡ Γ ++ Δ
      P = ap (Γ ++_) (++-idr Δ)
      s1 : Homₘ (Γ ++ ⊗₀ Δ ∷ []) w
      s1 = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} χ (⊗-arr Γ)
      s2 : Homₘ (Γ ++ (Δ ++ [])) w
      s2 = _∘ₘ_ {Θ = Γ} {Ξ = []} s1 (⊗-arr Δ)
      as2 : Homₘ ((Γ ++ (Δ ++ [])) ++ []) z
      as2 = _∘ₘ_ {Θ = []} {Ξ = []} a s2
      bd2 : Γ ++ (Δ ++ []) ≡ (Γ ++ (Δ ++ [])) ++ []
      bd2 = assocₘ-boundary [] Γ Δ [] []
      front-assoc : _∘ₘ_ {Θ = Γ} {Ξ = []}
              (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} a χ) (⊗-arr Γ))
              (⊗-arr Δ)
            ≡ subst (λ Ω → Homₘ Ω z) (sym bd2) as2
      front-assoc = ap (λ q → _∘ₘ_ {Θ = Γ} {Ξ = []} q (⊗-arr Δ)) (eqΓ a χ)
          ∙ from-pathp⁻ (assocₘ {Θ = []} {Ξ = []} {Φ = Γ} {Ψ = []} a s1 (⊗-arr Δ))

  -- Feeding the unit arrow ⊗-arr [] into μ [] Y's first slot yields the identity
  -- (μ [] Y restricts to ⊗-arr Y, and restrict is injective).
  μ-unit-l : (Y : List Obₘ)
           → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) (⊗-arr []) ≡ idₘ
  μ-unit-l Y = restrict.injective (
    restrict (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) (⊗-arr []))
      ≡⟨ restrict₂-μ [] Y ⟩
    ⊗-arr Y
      ≡˘⟨ restrict-id Y ⟩
    restrict (U.id {⊗₀ Y}) ∎)

  -- Left unit for the tensor of morphisms ([] ++ X = X definitionally).
  ⊗ₛ-idl : {X Y : List Obₘ} (f : U.Hom (⊗₀ X) (⊗₀ Y))
         → _⊗ₛ_ {[]} {[]} {X} {Y} U.id f ≡ f
  ⊗ₛ-idl {X} {Y} f = restrict.injective (
    restrict (_⊗ₛ_ {[]} {[]} {X} {Y} U.id f)
      ≡⟨ restrict.ε _ ⟩
    restrict₂.to (_∘ₘ_ {Θ = ⊗₀ [] ∷ []} {Ξ = []}
      (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) U.id) f)
      ≡⟨ ap (restrict {Γ = X}) idl-at-generators ⟩
    restrict f ∎)
    where
      i1' i0' : Homₘ (⊗₀ X ∷ []) (⊗₀ Y)
      i1' = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ X ∷ []}
              (_∘ₘ_ {Θ = ⊗₀ [] ∷ []} {Ξ = []} (μ [] Y) f) (⊗-arr [])
      i0' = _∘ₘ_ {Θ = []} {Ξ = []}
              (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) (⊗-arr [])) f
      interchange-idl : i1' ≡ i0'
      interchange-idl = sym (ic₂ (μ [] Y) (⊗-arr []) f)
      idl-at-generators : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ X ∷ []}
              (_∘ₘ_ {Θ = ⊗₀ [] ∷ []} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) U.id) f) (⊗-arr [])
            ≡ f
      idl-at-generators = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ X ∷ []}
                        (_∘ₘ_ {Θ = ⊗₀ [] ∷ []} {Ξ = []} q f) (⊗-arr []))
               (idₘl {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y))
          ∙ interchange-idl
          ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q f) (μ-unit-l Y)
          ∙ idₘr f

  -- The tensor of morphisms commutes with the comparison μ.
  ⊗ₛ-μ : {Γ Γ' Δ Δ' : List Obₘ}
         (f : U.Hom (⊗₀ Γ) (⊗₀ Γ')) (g : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
       → _∘ₘ_ {Θ = []} {Ξ = []} (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g) (μ Γ Δ)
         ≡ _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
             (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f) g
  ⊗ₛ-μ {Γ} {Γ'} {Δ} {Δ'} f g = restrict₂.injective (
    restrict₂.to (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) (μ Γ Δ))
      ≡⟨ restrict₂-nat (f ⊗ₛ g) (μ Γ Δ) ⟩
    subst (λ Ω → Homₘ Ω (⊗₀ (Γ' ++ Δ'))) (++-idr (Γ ++ Δ))
      (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) (restrict₂.to (μ Γ Δ)))
      ≡⟨ ap (λ q → subst (λ Ω → Homₘ Ω (⊗₀ (Γ' ++ Δ'))) (++-idr (Γ ++ Δ))
                     (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) q))
            (restrict₂-μ Γ Δ) ⟩
    restrict (f ⊗ₛ g)
      ≡⟨ restrict.ε _ ⟩
    restrict₂.to (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
      (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f) g) ∎)

  -- Bifunctoriality: the tensor preserves composition.
  ⊗ₛ-∘ : {Γ Γ' Γ'' Δ Δ' Δ'' : List Obₘ}
         (f  : U.Hom (⊗₀ Γ') (⊗₀ Γ'')) (f' : U.Hom (⊗₀ Γ) (⊗₀ Γ'))
         (g  : U.Hom (⊗₀ Δ') (⊗₀ Δ'')) (g' : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
       → _⊗ₛ_ {Γ} {Γ''} {Δ} {Δ''} (f U.∘ f') (g U.∘ g')
         ≡ (f ⊗ₛ g) U.∘ (f' ⊗ₛ g')
  ⊗ₛ-∘ {Γ} {Γ'} {Γ''} {Δ} {Δ'} {Δ''} f f' g g' = restrict.injective (
    restrict (_⊗ₛ_ {Γ} {Γ''} {Δ} {Δ''} (f U.∘ f') (g U.∘ g'))
      ≡⟨ restrict.ε _ ⟩
    restrict₂.to lhs-comp
      ≡⟨ ap restrict₂.to binary-eq ⟩
    restrict₂.to (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) rhs-comp)
      ≡⟨ restrict₂-nat (f ⊗ₛ g) rhs-comp ⟩
    subst (λ Ω → Homₘ Ω (⊗₀ (Γ'' ++ Δ''))) (++-idr (Γ ++ Δ))
      (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) (restrict₂.to rhs-comp))
      ≡˘⟨ ap (λ q → subst (λ Ω → Homₘ Ω (⊗₀ (Γ'' ++ Δ''))) (++-idr (Γ ++ Δ))
                      (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) q))
             (restrict.ε _) ⟩
    subst (λ Ω → Homₘ Ω (⊗₀ (Γ'' ++ Δ''))) (++-idr (Γ ++ Δ))
      (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) (restrict (f' ⊗ₛ g')))
      ≡˘⟨ restrict-nat (f ⊗ₛ g) (f' ⊗ₛ g') ⟩
    restrict ((f ⊗ₛ g) U.∘ (f' ⊗ₛ g')) ∎)
    where
      lhs-comp : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ'' ++ Δ''))
      lhs-comp = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
             (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} (μ Γ'' Δ'') (f U.∘ f')) (g U.∘ g')
      rhs-comp : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ' ++ Δ'))
      rhs-comp = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
             (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f') g'
      binary-eq : lhs-comp ≡ _∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) rhs-comp
      binary-eq = Lchain ∙ swap ∙ sym Rchain
        where
          μf : Homₘ (⊗₀ Γ' ∷ ⊗₀ Δ'' ∷ []) (⊗₀ (Γ'' ++ Δ''))
          μf = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} (μ Γ'' Δ'') f
          assoc-normalL : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ'' ++ Δ''))
          assoc-normalL = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                     (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                       (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f') g) g'
          assoc-normalR : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ'' ++ Δ''))
          assoc-normalR = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ' ∷ []} {Ξ = []} μf g) f') g'
          Lchain : lhs-comp ≡ assoc-normalL
          Lchain =
              ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q (g U.∘ g'))
                 (sym (assoc₀₀ (μ Γ'' Δ'') f f'))
            ∙ sym (assoc₁₀ (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f') g g')
          swap : assoc-normalL ≡ assoc-normalR
          swap = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g') (ic₂ μf f' g)
          Rchain : _∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) rhs-comp ≡ assoc-normalR
          Rchain =
              sym (assoc₀₁ (f ⊗ₛ g) (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f') g')
            ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g')
                 (sym (assoc₀₀ (f ⊗ₛ g) (μ Γ' Δ') f'))
            ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                          (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} q f') g')
                 (⊗ₛ-μ f g)

  -- The tensor as a (curried) bifunctor on Str.
  ⊗-functor : Functor (Str ×ᶜ Str) Str
  ⊗-functor .Functor.F₀ (Γ , Δ)            = Γ ++ Δ
  ⊗-functor .Functor.F₁ (f , g)            = f ⊗ₛ g
  ⊗-functor .Functor.F-id                  = ⊗ₛ-id _ _
  ⊗-functor .Functor.F-∘ (f , g) (f' , g') = ⊗ₛ-∘ f f' g g'

  ⊗ᵇ : Bifunctor Str Str Str
  ⊗ᵇ = Curry ⊗-functor

  private module B = Bifunctor ⊗ᵇ
  private module UMor = Cat.Morphism (Unary M)

  -- The associator/unitor structure maps: `path→iso` of a list-path, projected.
  ≅to : {A B : Obₘ} → A ≡ B → U.Hom A B
  ≅to p = UMor._≅_.to (path→iso p)
  ≅from : {A B : Obₘ} → A ≡ B → U.Hom B A
  ≅from p = UMor._≅_.from (path→iso p)
  ≅invl : {A B : Obₘ} (p : A ≡ B) → ≅to p U.∘ ≅from p ≡ U.id
  ≅invl p = UMor._≅_.invl (path→iso p)
  ≅invr : {A B : Obₘ} (p : A ≡ B) → ≅from p U.∘ ≅to p ≡ U.id
  ≅invr p = UMor._≅_.invr (path→iso p)

  -- path→iso of refl is the identity.
  ≅to-refl : {A : Obₘ} → ≅to (refl {x = A}) ≡ U.id
  ≅to-refl = ap UMor._≅_.to (transport-refl UMor.id-iso)

  -- path→iso sends sym to inverse.
  ≅from-to : {A B : Obₘ} (p : A ≡ B) → ≅from p ≡ ≅to (sym p)
  ≅from-to p = path→to-sym (Unary M) p

  -- The tautological PathP underlying a path→iso: over q, the identity
  -- deforms into ≅to q.  Composing a morphism (or any polymorphic operation)
  -- onto this filler under the interval is how the codomain-transport facts
  -- below are read off, with no path induction.
  ≅to-pathp : {A B : Obₘ} (q : A ≡ B)
            → PathP (λ i → U.Hom A (q i)) U.id (≅to q)
  ≅to-pathp q = Hom-pathp-reflr (Unary M) (U.idr _)

  -- Composing a path→iso onto a multimap transports its codomain: plug m
  -- into ≅to's filler under the interval.
  ≅to-∘ₘ : {Γ : List Obₘ} {A B : Obₘ} (q : A ≡ B) (m : Homₘ Γ A)
         → _∘ₘ_ {Θ = []} {Ξ = []} (≅to q) m
           ≡ subst (λ z → Homₘ (Γ ++ []) z) q (_∘ₘ_ {Θ = []} {Ξ = []} idₘ m)
  ≅to-∘ₘ q m =
    sym (from-pathp (λ i → _∘ₘ_ {Θ = []} {Ξ = []} (≅to-pathp q i) m))

  -- Transport bookkeeping: a transport of a two-index family along paths in
  -- both indices may be performed one index at a time, in either order.
  -- (The one genuinely path-inductive fact this file needs; stated for an
  -- arbitrary family, instantiated at Homₘ and its flip below.)
  private
    transport₂-split
      : ∀ {ℓa ℓb ℓf} {A : Type ℓa} {B : Type ℓb} (F : A → B → Type ℓf)
        {x x' : A} {y y' : B} (p : x ≡ x') (q : y ≡ y') (m : F x y)
      → transport (λ i → F (p i) (q i)) m
        ≡ subst (F x') q (subst (λ a → F a y) p m)
    transport₂-split F {x} {y = y} p q m =
      J (λ x' p → transport (λ i → F (p i) (q i)) m
                  ≡ subst (F x') q (subst (λ a → F a y) p m))
        (ap (subst (F x) q) (sym (transport-refl m)))
        p

  -- Transport over the 2-variable Homₘ family decomposes into domain then
  -- codomain, and the two one-sided substs commute.
  transp-decomp : {X X' : List Obₘ} {A A' : Obₘ}
                  (a : X ≡ X') (b : A ≡ A') (m : Homₘ X A)
                → transport (λ i → Homₘ (a i) (b i)) m
                  ≡ subst (λ z → Homₘ X' z) b (subst (λ Ω → Homₘ Ω A) a m)
  transp-decomp = transport₂-split Homₘ

  -- Expanding X to X++[] via the unitor iso, then the universal arrow of X,
  -- is the universal arrow of X++[].
  η-arr : (X : List Obₘ)
        → _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr X)))) (⊗-arr X)
          ≡ ⊗-arr (X ++ [])
  -- ≅to-∘ₘ turns the iso into a codomain transport of idₘ ∘ₘ ⊗-arr X; idₘr
  -- absorbs the idₘ (moving the domain X ← X++[]); the combined domain+codomain
  -- transport of ⊗-arr X is then exactly apd of ⊗-arr along sym (++-idr X)
  -- (transp-decomp splits it back into the two one-sided substs).
  η-arr X = ≅to-∘ₘ (ap ⊗₀ (sym (++-idr X))) (⊗-arr X)
          ∙ ap (subst (λ z → Homₘ (X ++ []) z) (ap ⊗₀ (sym (++-idr X))))
               (sym (from-pathp (symP (idₘr (⊗-arr X)))))
          ∙ sym (transp-decomp (sym (++-idr X)) (ap ⊗₀ (sym (++-idr X))) (⊗-arr X))
          ∙ from-pathp (apd (λ _ Γ → ⊗-arr Γ) (sym (++-idr X)))

  -- Feeding the unit arrow ⊗-arr [] into μ Y []'s SECOND slot yields the right
  -- unitor iso ηY (mirror of μ-unit-l; via ic₂ + restrict₂-μ + η-arr).
  μ-unit-r : (Y : List Obₘ)
           → _∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])
             ≡ ≅to (ap ⊗₀ (sym (++-idr Y)))
  μ-unit-r Y = restrict.injective
    ( ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr Y)) swap-eq
    ∙ sym (ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr Y)) (η-arr Y)) )
    where
      -- ic₂ reorders the plugs into restrict₂'s order; its trailing subst (over
      -- ap (Y ++_) (++-idr []) = refl) is the transport-refl.
      swap-eq : _∘ₘ_ {Θ = []} {Ξ = []}
                  (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])) (⊗-arr Y)
                ≡ ⊗-arr (Y ++ [])
      swap-eq =
          sym (ic₂ (μ Y []) (⊗-arr Y) (⊗-arr []))
        ∙ sym (transport-refl _)
        ∙ restrict₂-μ Y []

  -- Restricting the path→iso of q : A ≡ B recovers the universal arrow of B,
  -- reindexed along q: over q the iso deforms to the identity (a
  -- Hom-pathp-refll filler), restrict it under the interval, and at the far
  -- end restricting the identity is the universal arrow.
  restrict-α : {A B : List Obₘ} (q : A ≡ B)
             → restrict {A} (≅to (ap ⊗₀ q))
               ≡ subst (λ Ω → Homₘ Ω (⊗₀ B)) (sym q) (⊗-arr B)
  restrict-α {A} {B} q =
    from-pathp⁻ ((λ i → restrict {Γ = q i} (domfill i)) ▷ restrict-id B)
    where
      domfill : PathP (λ i → U.Hom (⊗₀ (q i)) (⊗₀ B)) (≅to (ap ⊗₀ q)) U.id
      domfill = Hom-pathp-refll (Unary M) (≅invl (ap ⊗₀ q))

  -- expand a, post-composed with the universal arrow, recovers a (reindexed).
  expand-arr : {Ω : List Obₘ} {z : Obₘ} (a : Homₘ Ω z)
             → _∘ₘ_ {Θ = []} {Ξ = []} (expand a) (⊗-arr Ω)
               ≡ subst (λ Ω' → Homₘ Ω' z) (sym (++-idr Ω)) a
  expand-arr {Ω} {z} a =
    sym (from-pathp (symP (to-pathp {A = λ i → Homₘ (++-idr Ω i) z} (restrict.ε a))))

  -- Feeding ⊗-arr[] into μY[]'s second slot past an arbitrary g' collapses (via
  -- ic₂ + μ-unit-r) to ηY ∘ₘ g'.
  μg-collapse : (Y Δ : List Obₘ) (g' : Homₘ Δ (⊗₀ Y))
              → _∘ₘ_ {Θ = Δ} {Ξ = []}
                  (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) g') (⊗-arr [])
                ≡ _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr Y)))) g'
  μg-collapse Y Δ g' =
      ic₂ (μ Y []) g' (⊗-arr [])
    ∙ ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} h g') (μ-unit-r Y)

  -- Right-unitor naturality: (f ⊗ id) ∘ ηX ≡ ηY ∘ f, where η is the ++[] iso.
  unitor-r-nat : {X Y : List Obₘ} (f : U.Hom (⊗₀ X) (⊗₀ Y))
               → _∘ₘ_ {Θ = []} {Ξ = []} (_⊗ₛ_ {X} {Y} {[]} {[]} f U.id)
                   (≅to (ap ⊗₀ (sym (++-idr X))))
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr Y)))) f
  unitor-r-nat {X} {Y} f = restrict.injective
    ( restrict-nat {Γ = X} fid ηX
    ∙ ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr X)) inner
    ∙ sym (restrict-nat {Γ = X} ηY f) )
    where
      ηX = ≅to (ap ⊗₀ (sym (++-idr X)))
      ηY = ≅to (ap ⊗₀ (sym (++-idr Y)))
      fid = _⊗ₛ_ {X} {Y} {[]} {[]} f U.id
      -- Via restrict₂-nat: fid ∘ₘ ⊗-arr(X++[]) transports restrict₂.to(fid∘ₘμX[]),
      -- which ⊗ₛ-μ rewrites to restrict₂.to(μY[]∘ₘf); `back` collapses that to
      -- ηY ∘ₘ (f ∘ₘ ⊗-arr X).
      residual : _∘ₘ_ {Θ = []} {Ξ = []} fid (⊗-arr (X ++ []))
               ≡ _∘ₘ_ {Θ = []} {Ξ = []} ηY (_∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X))
      residual =
          sym (transport⁻transport
                (ap (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr (X ++ []))) _)
        ∙ ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (sym (++-idr (X ++ []))))
             (sym RN' ∙ ap restrict₂.to ⊗ₛ-μ-idl)
        ∙ back
        where
          μYf : Homₘ (⊗₀ X ∷ ⊗₀ [] ∷ []) (⊗₀ (Y ++ []))
          μYf = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) f
          ⊗ₛ-μ-idl : _∘ₘ_ {Θ = []} {Ξ = []} fid (μ X []) ≡ μYf
          ⊗ₛ-μ-idl = ⊗ₛ-μ f U.id
                   ∙ idₘl {Θ = ⊗₀ X ∷ []} {Ξ = []} μYf
          RN' : restrict₂.to (_∘ₘ_ {Θ = []} {Ξ = []} fid (μ X []))
              ≡ subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr (X ++ []))
                  (_∘ₘ_ {Θ = []} {Ξ = []} fid (⊗-arr (X ++ [])))
          RN' = restrict₂-nat fid (μ X [])
              ∙ ap (λ h → subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr (X ++ []))
                            (_∘ₘ_ {Θ = []} {Ξ = []} fid h))
                   (restrict₂-μ X [])
          back : subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (sym (++-idr (X ++ [])))
                   (restrict₂.to μYf)
               ≡ _∘ₘ_ {Θ = []} {Ξ = []} ηY (_∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X))
          back =
              ap (subst B (sym (++-idr (X ++ [])))) (transport-refl μYf-plugged)
            ∙ from-pathp (hom-over (ap sym (++-idr-nat X)) chainB)
            where
              B : List Obₘ → Type h
              B = λ Ω → Homₘ Ω (⊗₀ (Y ++ []))
              gX : Homₘ (X ++ []) (⊗₀ Y)
              gX = _∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X)
              μYf-plugged : Homₘ (X ++ ([] ++ [])) (⊗₀ (Y ++ []))
              μYf-plugged = _∘ₘ_ {Θ = X} {Ξ = []}
                       (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} μYf (⊗-arr X)) (⊗-arr [])
              -- pull f's plug into μ Y [] (base path reconciled by ++-assoc-nil) …
              b1 : PathP (λ i → Homₘ (sym (++-idr X) i ++ ⊗₀ [] ∷ []) (⊗₀ (Y ++ [])))
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} μYf (⊗-arr X))
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) gX)
              b1 = hom-over (ap sym (++-assoc-nil X (⊗₀ [] ∷ [])))
                     (assoc₀₀ (μ Y []) f (⊗-arr X))
              -- … plug ⊗-arr [] along it, and collapse with μg-collapse.
              chainB : PathP (λ i → Homₘ (sym (++-idr X) i ++ [] ++ []) (⊗₀ (Y ++ [])))
                     μYf-plugged
                     (_∘ₘ_ {Θ = []} {Ξ = []} ηY gX)
              chainB = ∘ₘ-pathp (sym (++-idr X)) refl refl b1 refl
                     ▷ μg-collapse Y (X ++ []) gX
      inner : _∘ₘ_ {Θ = []} {Ξ = []} fid (restrict {X} ηX)
            ≡ _∘ₘ_ {Θ = []} {Ξ = []} ηY (restrict {X} f)
      inner =
          ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} fid q)
             (ap (subst (λ Ω → Homₘ Ω (⊗₀ (X ++ []))) (++-idr X)) (η-arr X))
        ∙ Rep.∘ₘ-substr M fid (++-idr X) (⊗-arr (X ++ []))
        ∙ ap (subst (λ Ω → Homₘ ([] ++ Ω ++ []) (⊗₀ (Y ++ []))) (++-idr X)) residual
        ∙ sym (Rep.∘ₘ-substr M ηY (++-idr X) (_∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X)))

  -- ============ Ternary μ-hexagon machinery (for assoc-nat) ============

  -- Feeding μ Δ Ε into the single slot of `expand (restrict₂.to b)` recovers b:
  -- restrict₂ then expand then re-split by μ is the identity.
  expandμ : {Δ Ε M : List Obₘ} (b : Homₘ (⊗₀ Δ ∷ ⊗₀ Ε ∷ []) (⊗₀ M))
          → _∘ₘ_ {Θ = []} {Ξ = []} (expand (restrict₂.to {Δ} {Ε} b)) (μ Δ Ε) ≡ b
  expandμ {Δ} {Ε} {M} b = restrict₂.injective
    ( restrict₂-nat u (μ Δ Ε)
    ∙ ap (λ h → subst B (++-idr (Δ ++ Ε)) (_∘ₘ_ {Θ = []} {Ξ = []} u h)) (restrict₂-μ Δ Ε)
    ∙ ap (subst B (++-idr (Δ ++ Ε))) (expand-arr (restrict₂.to {Δ} {Ε} b))
    ∙ subst-cancel )
    where
      B : List Obₘ → Type h
      B = λ Ω → Homₘ Ω (⊗₀ M)
      u : Homₘ (⊗₀ (Δ ++ Ε) ∷ []) (⊗₀ M)
      u = expand (restrict₂.to {Δ} {Ε} b)
      subst-cancel : subst B (++-idr (Δ ++ Ε)) (subst B (sym (++-idr (Δ ++ Ε))) (restrict₂.to {Δ} {Ε} b))
                   ≡ restrict₂.to {Δ} {Ε} b
      subst-cancel =
        transport⁻transport (sym (ap B (++-idr (Δ ++ Ε)))) (restrict₂.to {Δ} {Ε} b)

  -- Collapsing μ Δ Ε fed ⊗-arr Ε (slot 2) then ⊗-arr Δ (slot 1) — the reversed
  -- plug order — yields ⊗-arr (Δ ++ Ε), as a PathP over ap (Δ ++_) (++-idr Ε):
  -- ic₂ reorders the plugs into restrict₂'s order, and restrict₂-μ collapses.
  μ-block : (Δ Ε : List Obₘ)
          → PathP (λ i → Homₘ (ap (Δ ++_) (++-idr Ε) i) (⊗₀ (Δ ++ Ε)))
              (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []}
                (_∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)) (⊗-arr Δ))
              (⊗-arr (Δ ++ Ε))
  μ-block Δ Ε =
    sym (ic₂ (μ Δ Ε) (⊗-arr Δ) (⊗-arr Ε))
      ◁ to-pathp {A = λ i → Homₘ (ap (Δ ++_) (++-idr Ε) i) (⊗₀ (Δ ++ Ε))}
          (restrict₂-μ Δ Ε)

  -- restrict₃ plugs universal arrows on the DOMAIN, so a codomain post-comp
  -- commutes out as a codomain-subst.
  restrict₃-α : {Γ Δ Ε : List Obₘ} {C C' : Obₘ}
                (q : C ≡ C') (W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) C)
              → restrict₃.to {Γ} {Δ} {Ε} {C'} (_∘ₘ_ {Θ = []} {Ξ = []} (≅to q) W)
                ≡ subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) q (restrict₃.to {Γ} {Δ} {Ε} {C} W)
  restrict₃-α {Γ} {Δ} {Ε} {C} q W =
      sym (from-pathp (λ i → restrict₃.to {Γ} {Δ} {Ε}
            (_∘ₘ_ {Θ = []} {Ξ = []} (≅to-pathp q i) W)))
    ∙ ap (subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) q)
         (ap (restrict₃.to {Γ} {Δ} {Ε}) (idₘr W))

  -- Split a binary restriction into a ternary one by plugging μ Δ Ε into the
  -- second (merged) slot.  Each algebraic move is one named PathP:
  --   s1  pull ⊗-arr Ε into μ              (assoc₁₁)
  --   s2  plug ⊗-arr Δ along s1            (∘ₘ-pathp, free)
  --   s3  pull ⊗-arr Δ into μ ∘ ⊗-arr Ε    (assoc₁₀)
  --   s4  collapse the μ-block             (μ-block)
  --   s5  plug s4 into χ                   (∘ₘ-pathp, free)
  --   t*  plug ⊗-arr Γ along s2, s3, s5    (∘ₘ-pathp, free)
  --   ic₂ reorder the Γ/(Δ++Ε) plugs       (homogeneous)
  -- composed with ∙P and reconciled once against the canonical list-path
  -- (spine-coh, whose content is the spine lemma splitμ-coh).
  splitμ : {Γ Δ Ε : List Obₘ} {z : Obₘ} (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ (Δ ++ Ε) ∷ []) z)
         → restrict₂.to {Γ} {Δ ++ Ε} χ
           ≡ restrict₃.to {Γ} {Δ} {Ε} (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ (μ Δ Ε))
  splitμ {Γ} {Δ} {Ε} {z} χ = sym (from-pathp (hom-over spine-coh chain))
    where
      BΩ : List Obₘ → Type _
      BΩ Ω = Homₘ Ω z
      μᵍ    = μ Δ Ε
      arrDE = ⊗-arr (Δ ++ Ε)
      W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z
      W = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μᵍ
      μEE : Homₘ (⊗₀ Δ ∷ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μEE = _∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} μᵍ (⊗-arr Ε)
      μbb : Homₘ (Δ ++ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μbb = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} μEE (⊗-arr Δ)
      -- canonical list paths
      P-DE = ap (Δ ++_) (++-idr Ε)
      q̄    = sym (++-assoc Ε [] [])
      r̄    = sym (++-assoc Δ (Ε ++ []) [])
      i2 = ap (Δ ++_) q̄
      i5 = ap (_++ []) P-DE
      p2 = ap (Γ ++_) i2
      p3 = ap (Γ ++_) r̄
      p5 = ap (Γ ++_) i5
      P₂ap = ap (Γ ++_) (++-idr (Δ ++ Ε))
      P₃   = ap (Γ ++_) P-DE
      -- s1: pull ⊗-arr Ε into μ.
      s1 : PathP (λ i → Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ q̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE)
      s1 = assoc₁₁ χ μᵍ (⊗-arr Ε)
      -- s2: plug ⊗-arr Δ along s1.
      s2 : PathP (λ i → Homₘ (⊗₀ Γ ∷ Δ ++ q̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE) (⊗-arr Δ))
      s2 = ∘ₘ-pathp refl q̄ refl s1 refl
      -- s3: pull ⊗-arr Δ into μEE.
      s3 : PathP (λ i → Homₘ (⊗₀ Γ ∷ r̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE) (⊗-arr Δ))
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μbb)
      s3 = assoc₁₀ χ μEE (⊗-arr Δ)
      -- s4: the μ-block collapse.  s5: plug it into χ.
      s5 : PathP (λ i → Homₘ (⊗₀ Γ ∷ P-DE i ++ []) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μbb)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ arrDE)
      s5 = ∘ₘ-pathp refl refl P-DE refl (μ-block Δ Ε)
      -- t*: plug ⊗-arr Γ along s2, s3, s5.
      t2 : PathP (λ i → Homₘ (p2 i) z) _ _
      t2 = ∘ₘ-pathp refl i2 refl s2 (λ _ → ⊗-arr Γ)
      t3 : PathP (λ i → Homₘ (p3 i) z) _ _
      t3 = ∘ₘ-pathp refl r̄ refl s3 (λ _ → ⊗-arr Γ)
      t5 : PathP (λ i → Homₘ (p5 i) z) _ _
      t5 = ∘ₘ-pathp refl i5 refl s5 (λ _ → ⊗-arr Γ)
      canon : Homₘ (Γ ++ ((Δ ++ Ε) ++ [])) z
      canon = _∘ₘ_ {Θ = Γ} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ (Δ ++ Ε) ∷ []} χ (⊗-arr Γ)) arrDE
      -- assemble; reorder the Γ/(Δ++Ε) plugs; land on restrict₂.to χ.
      chain : PathP (λ i → Homₘ ((((p2 ∙ p3) ∙ p5) ∙ P₂ap) i) z)
                (_∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
                  (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
                  (⊗-arr Γ))
                (restrict₂.to {Γ} {Δ ++ Ε} χ)
      chain =
        _∙P_ {B = BΩ} {p = (p2 ∙ p3) ∙ p5} {q = P₂ap}
          ( (_∙P_ {B = BΩ} {p = p2 ∙ p3} {q = p5}
              (_∙P_ {B = BΩ} {p = p2} {q = p3} t2 t3)
              t5)
            ▷ sym (ic₂ χ (⊗-arr Γ) arrDE) )
          (transport-filler (λ i → BΩ (P₂ap i)) canon)
      -- the single spine reconciliation
      spine-coh : ((p2 ∙ p3) ∙ p5) ∙ P₂ap ≡ P₃
      spine-coh =
          ap (λ t → (t ∙ p5) ∙ P₂ap) (sym (ap-∙ (Γ ++_) i2 r̄))
        ∙ ap (_∙ P₂ap) (sym (ap-∙ (Γ ++_) (i2 ∙ r̄) i5))
        ∙ sym (ap-∙ (Γ ++_) ((i2 ∙ r̄) ∙ i5) (++-idr (Δ ++ Ε)))
        ∙ ap (ap (Γ ++_)) (splitμ-coh Δ Ε)

  -- Split a binary restriction into a ternary one by plugging μ Γ Δ into the
  -- FIRST (merged) slot.  Mirror of splitμ:
  --   u1  swap χ's ⊗Ε-plug before μ Γ Δ         (ic₂, homogeneous)
  --   u2  pull ⊗-arr Δ into μ                   (assoc₀₁, u1 folded in)
  --   w2  plug ⊗-arr Γ along u2                 (∘ₘ-pathp, free)
  --   w3  pull ⊗-arr Γ into μ ∘ ⊗-arr Δ         (assoc₀₀)
  --   w5  plug the μ-block collapse into χE, then reorder the (Γ++Δ)/Ε plugs
  --       back (∘ₘ-pathp + μ-block, then ic₂)
  -- composed with ∙P and reconciled once against ++-assoc's spine
  -- (spine-coh, whose content is the spine lemma splitμ-l-coh).
  splitμ-l : {Γ Δ Ε : List Obₘ} {z : Obₘ} (χ : Homₘ (⊗₀ (Γ ++ Δ) ∷ ⊗₀ Ε ∷ []) z)
           → restrict₃.to {Γ} {Δ} {Ε} (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ (μ Γ Δ))
             ≡ subst (λ Ω → Homₘ Ω z) (++-assoc Γ Δ Ε) (restrict₂.to {Γ ++ Δ} {Ε} χ)
  splitμ-l {Γ} {Δ} {Ε} {z} χ = from-pathp (hom-over spine-coh chain)
    where
      BΩ : List Obₘ → Type _
      BΩ Ω = Homₘ Ω z
      μᵍ    = μ Γ Δ
      arrGD = ⊗-arr (Γ ++ Δ)
      W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z
      W = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ μᵍ
      χE : Homₘ (⊗₀ (Γ ++ Δ) ∷ (Ε ++ [])) z
      χE = _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} χ (⊗-arr Ε)
      μD : Homₘ (⊗₀ Γ ∷ (Δ ++ [])) (⊗₀ (Γ ++ Δ))
      μD = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} μᵍ (⊗-arr Δ)
      μbb : Homₘ (Γ ++ (Δ ++ [])) (⊗₀ (Γ ++ Δ))
      μbb = _∘ₘ_ {Θ = []} {Ξ = Δ ++ []} μD (⊗-arr Γ)
      -- canonical list paths
      P-GD = ap (Γ ++_) (++-idr Δ)
      r̄    = sym (++-assoc Δ [] (Ε ++ []))
      p2 = ap (Γ ++_) r̄
      p3 = sym (++-assoc Γ (Δ ++ []) (Ε ++ []))
      p5 = ap (_++ (Ε ++ [])) P-GD
      P₂' = ap ((Γ ++ Δ) ++_) (++-idr Ε)
      P₃  = ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))
      -- u2: pull ⊗-arr Δ into μ, with the ⊗Ε-swap (ic₂) folded into i0.
      u2 : PathP (λ i → Homₘ (⊗₀ Γ ∷ r̄ i) z)
             (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
             (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μD)
      u2 = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} q (⊗-arr Δ))
              (ic₂ χ μᵍ (⊗-arr Ε))
             ◁ assoc₀₁ χE μᵍ (⊗-arr Δ)
      -- w2: plug ⊗-arr Γ along u2.
      w2 : PathP (λ i → Homₘ (Γ ++ r̄ i) z)
             (_∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
               (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                 (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
               (⊗-arr Γ))
             (_∘ₘ_ {Θ = []} {Ξ = (Δ ++ []) ++ (Ε ++ [])}
               (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μD) (⊗-arr Γ))
      w2 = ∘ₘ-pathp refl r̄ refl u2 refl
      -- w3: pull ⊗-arr Γ into μD.
      w3 : PathP (λ i → Homₘ (p3 i) z)
             (_∘ₘ_ {Θ = []} {Ξ = (Δ ++ []) ++ (Ε ++ [])}
               (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μD) (⊗-arr Γ))
             (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μbb)
      w3 = assoc₀₀ χE μD (⊗-arr Γ)
      canon : Homₘ ((Γ ++ Δ) ++ (Ε ++ [])) z
      canon = _∘ₘ_ {Θ = Γ ++ Δ} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ arrGD) (⊗-arr Ε)
      -- w5: plug the μ-block collapse into χE, then reorder the plugs back.
      w5 : PathP (λ i → Homₘ (P-GD i ++ (Ε ++ [])) z)
             (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μbb)
             canon
      w5 = ∘ₘ-pathp refl refl P-GD (λ _ → χE) (μ-block Γ Δ)
             ▷ sym (ic₂ χ arrGD (⊗-arr Ε))
      -- assemble; land on restrict₂.to χ, then follow its ++-assoc transport.
      chain : PathP (λ i → Homₘ (((((p2 ∙ p3) ∙ p5) ∙ P₂') ∙ ++-assoc Γ Δ Ε) i) z)
                (_∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
                  (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ))
                  (⊗-arr Γ))
                (subst BΩ (++-assoc Γ Δ Ε) (restrict₂.to {Γ ++ Δ} {Ε} χ))
      chain =
        _∙P_ {B = BΩ} {p = ((p2 ∙ p3) ∙ p5) ∙ P₂'} {q = ++-assoc Γ Δ Ε}
          ( _∙P_ {B = BΩ} {p = (p2 ∙ p3) ∙ p5} {q = P₂'}
              (_∙P_ {B = BΩ} {p = p2 ∙ p3} {q = p5}
                (_∙P_ {B = BΩ} {p = p2} {q = p3} w2 w3)
                w5)
              (transport-filler (λ i → BΩ (P₂' i)) canon) )
          (transport-filler (λ i → BΩ (++-assoc Γ Δ Ε i)) (restrict₂.to {Γ ++ Δ} {Ε} χ))
      -- the single spine reconciliation
      spine-coh : (((p2 ∙ p3) ∙ p5) ∙ P₂') ∙ ++-assoc Γ Δ Ε ≡ P₃
      spine-coh = splitμ-l-coh Γ Δ Ε

  -- Domain-subst and codomain-subst of a Homₘ commute (independent indices).
  subst-dom-cod : {X X' : List Obₘ} {A A' : Obₘ} (p : X ≡ X') (q : A ≡ A') (m : Homₘ X A)
    → subst (λ Ω → Homₘ Ω A') p (subst (λ z → Homₘ X z) q m)
      ≡ subst (λ z → Homₘ X' z) q (subst (λ Ω → Homₘ Ω A) p m)
  subst-dom-cod p q m =
      sym (transport₂-split (λ z Ω → Homₘ Ω z) q p m)
    ∙ transport₂-split Homₘ p q m

  -- The pure μ-hexagon (no morphisms): the two association orders of the triple
  -- comparison map agree up to the associator.  Both restrict to ⊗-arr; the
  -- residual is the ⊗-arr coherence under ++-assoc.
  μ-hex : (A B C : List Obₘ)
        → _∘ₘ_ {Θ = ⊗₀ A ∷ []} {Ξ = []} (μ A (B ++ C)) (μ B C)
          ≡ _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (++-assoc A B C)))
              (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ C ∷ []} (μ (A ++ B) C) (μ A B))
  μ-hex A B C = restrict₃.injective {A} {B} {C}
    ( sym (splitμ {A} {B} {C} (μ A (B ++ C)))
    ∙ restrict₂-μ A (B ++ C)
    ∙ arr-coh
    ∙ ap (subst (λ z → Homₘ (A ++ (B ++ C)) z) (ap ⊗₀ (++-assoc A B C))) (sym MBcomp)
    ∙ sym (restrict₃-α {A} {B} {C} (ap ⊗₀ (++-assoc A B C))
             (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ C ∷ []} (μ (A ++ B) C) (μ A B))) )
    where
      MBcomp : restrict₃.to {A} {B} {C} (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ C ∷ []} (μ (A ++ B) C) (μ A B))
             ≡ subst (λ Ω → Homₘ Ω (⊗₀ ((A ++ B) ++ C))) (++-assoc A B C) (⊗-arr ((A ++ B) ++ C))
      MBcomp = splitμ-l {A} {B} {C} (μ (A ++ B) C)
             ∙ ap (subst (λ Ω → Homₘ Ω (⊗₀ ((A ++ B) ++ C))) (++-assoc A B C)) (restrict₂-μ (A ++ B) C)
      arr-coh : ⊗-arr (A ++ (B ++ C))
              ≡ subst (λ z → Homₘ (A ++ (B ++ C)) z) (ap ⊗₀ (++-assoc A B C))
                  (subst (λ Ω → Homₘ Ω (⊗₀ ((A ++ B) ++ C))) (++-assoc A B C) (⊗-arr ((A ++ B) ++ C)))
      arr-coh = sym (from-pathp (apd (λ _ Γ → ⊗-arr Γ) (++-assoc A B C)))
              ∙ transp-decomp (++-assoc A B C) (ap ⊗₀ (++-assoc A B C)) (⊗-arr ((A ++ B) ++ C))

  -- Associator naturality: the abstract μ-hexagon at the level of morphisms.
  assoc-nat : {Γ Δ Ε Γ' Δ' Ε' : List Obₘ}
              (f₁ : U.Hom (⊗₀ Γ) (⊗₀ Γ')) (f₂ : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
              (f₃ : U.Hom (⊗₀ Ε) (⊗₀ Ε'))
            → _∘ₘ_ {Θ = []} {Ξ = []}
                (_⊗ₛ_ {Γ} {Γ'} {Δ ++ Ε} {Δ' ++ Ε'} f₁ (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃))
                (≅to (ap ⊗₀ (++-assoc Γ Δ Ε)))
              ≡ _∘ₘ_ {Θ = []} {Ξ = []}
                (≅to (ap ⊗₀ (++-assoc Γ' Δ' Ε')))
                (_⊗ₛ_ {Γ ++ Δ} {Γ' ++ Δ'} {Ε} {Ε'} (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f₁ f₂) f₃)
  assoc-nat {Γ} {Δ} {Ε} {Γ'} {Δ'} {Ε'} f₁ f₂ f₃ = restrict.injective
    ( restrict-nat {Γ = (Γ ++ Δ) ++ Ε} FA α
    ∙ ap (subst (λ Ω → Homₘ Ω (⊗₀ (Γ' ++ Δ' ++ Ε'))) (++-idr ((Γ ++ Δ) ++ Ε))) core-inner
    ∙ sym (restrict-nat {Γ = (Γ ++ Δ) ++ Ε} α' FB) )
    where
      FA = _⊗ₛ_ {Γ} {Γ'} {Δ ++ Ε} {Δ' ++ Ε'} f₁ (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃)
      FB = _⊗ₛ_ {Γ ++ Δ} {Γ' ++ Δ'} {Ε} {Ε'} (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f₁ f₂) f₃
      α  = ≅to (ap ⊗₀ (++-assoc Γ Δ Ε))
      α' = ≅to (ap ⊗₀ (++-assoc Γ' Δ' Ε'))
      core-inner : _∘ₘ_ {Θ = []} {Ξ = []} FA (restrict {(Γ ++ Δ) ++ Ε} α)
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' (restrict {(Γ ++ Δ) ++ Ε} FB)
      aFA : Homₘ (Γ ++ (Δ ++ Ε)) (⊗₀ (Γ' ++ (Δ' ++ Ε')))
      aFA = restrict₂.to {Γ} {Δ ++ Ε}
              (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ (Δ' ++ Ε') ∷ []} (μ Γ' (Δ' ++ Ε')) f₁)
                (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃))
      aFB : Homₘ ((Γ ++ Δ) ++ Ε) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      aFB = restrict₂.to {Γ ++ Δ} {Ε}
              (_∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []}
                (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} (μ (Γ' ++ Δ') Ε') (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f₁ f₂))
                f₃)
      -- Ternary (un-tensored) form of aFA: the right-nested comparison map with
      -- μ Γ' (Δ'++Ε') outermost and μ Δ' Ε' inner, fed the fᵢ's.
      a-A : Homₘ (⊗₀ Γ ∷ ⊗₀ (Δ' ++ Ε') ∷ []) (⊗₀ (Γ' ++ (Δ' ++ Ε')))
      a-A = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ (Δ' ++ Ε') ∷ []} (μ Γ' (Δ' ++ Ε')) f₁
      inner-A : Homₘ (⊗₀ Δ ∷ ⊗₀ Ε ∷ []) (⊗₀ (Δ' ++ Ε'))
      inner-A = _∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []}
                  (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} (μ Δ' Ε') f₂) f₃
      χ-A : Homₘ (⊗₀ Γ ∷ ⊗₀ (Δ ++ Ε) ∷ []) (⊗₀ (Γ' ++ (Δ' ++ Ε')))
      χ-A = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃)
      WA3 : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) (⊗₀ (Γ' ++ (Δ' ++ Ε')))
      WA3 = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A inner-A
      WA3-eq : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ-A (μ Δ Ε) ≡ WA3
      WA3-eq =
          assoc₁₀ a-A (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃) (μ Δ Ε)
        ∙ ap (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A) (expandμ {Δ} {Ε} inner-A)
      fusionA : restrict₃.to {Γ} {Δ} {Ε} WA3 ≡ aFA
      fusionA = ap (restrict₃.to {Γ} {Δ} {Ε}) (sym WA3-eq) ∙ sym (splitμ χ-A)

      -- Ternary (un-tensored) form of aFB: μ (Γ'++Δ') Ε' outermost, μ Γ' Δ' inner.
      μGD' : Homₘ (⊗₀ (Γ' ++ Δ') ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      μGD' = μ (Γ' ++ Δ') Ε'
      f12 : U.Hom (⊗₀ (Γ ++ Δ)) (⊗₀ (Γ' ++ Δ'))
      f12 = _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f₁ f₂
      a-B : Homₘ (⊗₀ (Γ ++ Δ) ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      a-B = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' f12
      χ-B : Homₘ (⊗₀ (Γ ++ Δ) ∷ ⊗₀ Ε ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      χ-B = _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} a-B f₃
      inner-B : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ' ++ Δ'))
      inner-B = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                  (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f₁) f₂
      b1 : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      b1 = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' inner-B
      WB3 : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      WB3 = _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} b1 f₃
      WB3-eq : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ-B (μ Γ Δ) ≡ WB3
      WB3-eq =
          sym (ic₂ a-B (μ Γ Δ) f₃)
        ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃)
             ( assoc₀₀ μGD' f12 (μ Γ Δ)
             ∙ ap (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD') (expandμ {Γ} {Δ} inner-B) )
      fusionB : restrict₃.to {Γ} {Δ} {Ε} WB3
              ≡ subst (λ Ω → Homₘ Ω (⊗₀ ((Γ' ++ Δ') ++ Ε'))) (++-assoc Γ Δ Ε) aFB
      fusionB = ap (restrict₃.to {Γ} {Δ} {Ε}) (sym WB3-eq) ∙ splitμ-l χ-B

      -- Thread f₁,f₂,f₃ onto the pure-hexagon maps MA', MB' (all boundaries refl,
      -- single-object slots) to recover WA3, WB3.
      MA' : Homₘ (⊗₀ Γ' ∷ ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []) (⊗₀ (Γ' ++ (Δ' ++ Ε')))
      MA' = _∘ₘ_ {Θ = ⊗₀ Γ' ∷ []} {Ξ = []} (μ Γ' (Δ' ++ Ε')) (μ Δ' Ε')
      μΔ'f₂ : Homₘ (⊗₀ Δ ∷ ⊗₀ Ε' ∷ []) (⊗₀ (Δ' ++ Ε'))
      μΔ'f₂ = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} (μ Δ' Ε') f₂
      thread-A : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                   (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MA' f₁) f₂) f₃
               ≡ WA3
      thread-A =
          ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂) f₃) step1
        ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃) step2
        ∙ step3
        where
          step1 : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MA' f₁
                ≡ _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A (μ Δ' Ε')
          step1 = sym (ic₂ (μ Γ' (Δ' ++ Ε')) f₁ (μ Δ' Ε'))
          step2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A (μ Δ' Ε')) f₂
                ≡ _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A μΔ'f₂
          step2 = assoc₁₀ a-A (μ Δ' Ε') f₂
          step3 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A μΔ'f₂) f₃
                ≡ WA3
          step3 = assoc₁₁ a-A μΔ'f₂ f₃

      MB' : Homₘ (⊗₀ Γ' ∷ ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      MB' = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' (μ Γ' Δ')
      μΓ'f₁ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ' ∷ []) (⊗₀ (Γ' ++ Δ'))
      μΓ'f₁ = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f₁
      thread-B : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                   (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MB' f₁) f₂) f₃
               ≡ WB3
      thread-B =
          ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂) f₃) tstep1
        ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃) tstep2
        where
          tstep1 : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MB' f₁
                 ≡ _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' μΓ'f₁
          tstep1 = assoc₀₀ μGD' (μ Γ' Δ') f₁
          tstep2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' μΓ'f₁) f₂
                 ≡ b1
          tstep2 = assoc₀₁ μGD' μΓ'f₁ f₂

      -- α' (codomain iso) commutes past the three domain f-plugs
      -- (assoc₀₀ / assoc₀₁ / assoc₀₂).
      T3MB' : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      T3MB' = _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                  (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MB' f₁) f₂) f₃
      MBf₁ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      MBf₁ = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} MB' f₁
      MBf₁f₂ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      MBf₁f₂ = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} MBf₁ f₂
      commute : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                  (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                    (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []}
                      (_∘ₘ_ {Θ = []} {Ξ = []} α' MB') f₁) f₂) f₃
              ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' T3MB'
      commute =
          ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂) f₃) cstep1
        ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃) cstep2
        ∙ cstep3
        where
          cstep1 : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} α' MB') f₁
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁
          cstep1 = assoc₀₀ α' MB' f₁
          cstep2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁) f₂
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁f₂
          cstep2 = assoc₀₁ α' MBf₁ f₂
          cstep3 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁f₂) f₃
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' T3MB'
          cstep3 = assoc₀₂ α' MBf₁f₂ f₃

      ternary-hex : WA3 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' WB3
      ternary-hex =
          sym thread-A
        ∙ ap (λ X → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                         (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} X f₁) f₂) f₃)
             (μ-hex Γ' Δ' Ε')
        ∙ commute
        ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} α' q) thread-B

      -- The μ-hexagon (with morphisms): the two association orders of the triple
      -- tensor, restricted to the generators, agree up to the associator α'.
      μ-hex-f : subst (λ Ω → Homₘ ([] ++ Ω ++ []) (⊗₀ (Γ' ++ Δ' ++ Ε'))) (sym (++-assoc Γ Δ Ε))
                  (subst (λ Ω' → Homₘ Ω' (⊗₀ (Γ' ++ Δ' ++ Ε'))) (sym (++-idr (Γ ++ Δ ++ Ε))) aFA)
              ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' aFB
      μ-hex-f =
          ap (λ w → subst (λ Ω → Homₘ ([] ++ Ω ++ []) cod) (sym (++-assoc Γ Δ Ε))
                      (subst (λ Ω' → Homₘ Ω' cod) (sym (++-idr (Γ ++ (Δ ++ Ε)))) w))
             aFA-eq
        ∙ ap (subst (λ Ω → Homₘ ([] ++ Ω ++ []) cod) (sym (++-assoc Γ Δ Ε)))
             (subst-dom-cod (sym (++-idr (Γ ++ (Δ ++ Ε)))) cod-path aFB')
        ∙ subst-dom-cod (ap (_++ []) (sym (++-assoc Γ Δ Ε))) cod-path
            (subst Cod (sym (++-idr (Γ ++ (Δ ++ Ε)))) aFB')
        ∙ ap (subst (λ z → Homₘ (((Γ ++ Δ) ++ Ε) ++ []) z) cod-path) mergechain
        ∙ sym RHS-eq
        where
          cod : Obₘ
          cod = ⊗₀ (Γ' ++ (Δ' ++ Ε'))
          Cod : List Obₘ → Type h
          Cod = λ Ω → Homₘ Ω (⊗₀ ((Γ' ++ Δ') ++ Ε'))
          cod-path : ⊗₀ ((Γ' ++ Δ') ++ Ε') ≡ cod
          cod-path = ap ⊗₀ (++-assoc Γ' Δ' Ε')
          aFB' : Homₘ (Γ ++ (Δ ++ Ε)) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
          aFB' = subst Cod (++-assoc Γ Δ Ε) aFB
          aFA-eq : aFA ≡ subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) cod-path aFB'
          aFA-eq = sym fusionA
                 ∙ ap (restrict₃.to {Γ} {Δ} {Ε}) ternary-hex
                 ∙ restrict₃-α {Γ} {Δ} {Ε} cod-path WB3
                 ∙ ap (subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) cod-path) fusionB
          mergechain : subst Cod (ap (_++ []) (sym (++-assoc Γ Δ Ε)))
                         (subst Cod (sym (++-idr (Γ ++ (Δ ++ Ε)))) aFB')
                     ≡ subst Cod (sym (++-idr ((Γ ++ Δ) ++ Ε))) aFB
          mergechain =
              ap (subst Cod (ap (_++ []) (sym (++-assoc Γ Δ Ε))))
                 (sym (subst-∙ Cod (++-assoc Γ Δ Ε) (sym (++-idr (Γ ++ (Δ ++ Ε)))) aFB))
            ∙ sym (subst-∙ Cod (++-assoc Γ Δ Ε ∙ sym (++-idr (Γ ++ (Δ ++ Ε))))
                     (ap (_++ []) (sym (++-assoc Γ Δ Ε))) aFB)
            ∙ ap (λ p → subst Cod p aFB)
                 (idr-assoc-coh (++-assoc Γ Δ Ε))
          RHS-eq : _∘ₘ_ {Θ = []} {Ξ = []} α' aFB
                 ≡ subst (λ z → Homₘ (((Γ ++ Δ) ++ Ε) ++ []) z) cod-path
                     (subst Cod (sym (++-idr ((Γ ++ Δ) ++ Ε))) aFB)
          RHS-eq = ≅to-∘ₘ cod-path aFB
                 ∙ ap (subst (λ z → Homₘ (((Γ ++ Δ) ++ Ε) ++ []) z) cod-path)
                      (sym (from-pathp (symP (idₘr aFB))))
      core-inner =
          ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} FA h) (restrict-α (++-assoc Γ Δ Ε))
        ∙ Rep.∘ₘ-substr M FA (sym (++-assoc Γ Δ Ε)) (⊗-arr (Γ ++ (Δ ++ Ε)))
        ∙ ap (subst (λ Ω → Homₘ ([] ++ Ω ++ []) (⊗₀ (Γ' ++ Δ' ++ Ε'))) (sym (++-assoc Γ Δ Ε)))
             (expand-arr aFA)
        ∙ μ-hex-f
        ∙ sym (ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} α' h) (restrict.ε aFB))

  -- The bifunctor's pair action (f ◆ g = (f ◀ _) ∘ (_ ▶ g)) is our ⊗ₛ
  -- (the whiskerings themselves are ⊗ₛ with an identity, definitionally).
  ◆≡⊗ₛ : {Γ Γ' Δ Δ' : List Obₘ}
         (f : U.Hom (⊗₀ Γ) (⊗₀ Γ')) (g : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
       → B._◆_ f g ≡ _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g
  ◆≡⊗ₛ {Γ} {Γ'} {Δ} {Δ'} f g =
      sym (⊗ₛ-∘ f U.id U.id g)
    ∙ ap₂ (λ a b → _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} a b) (U.idr f) (U.idl g)

  -- ==========================================================================
  -- The strict monoidal structure, and its strictness, via the coherent-
  -- path-monoid constructor (Monoidal.Strict.from-path-monoid).  Objects are
  -- lists, tensor is concatenation, Unit is []; the left unitor is the
  -- identity ([] ++ X = X definitionally) and the right unitor/associator are
  -- the path→isos of ++-idr/++-assoc.  We supply the three structural
  -- natural isomorphisms — their naturality squares (⊗ₛ-idl, unitor-r-nat,
  -- assoc-nat) are the substantive content — together with the coherent
  -- path-monoid on List Obₘ (++-assoc / refl / ++-idr, plus the spine-level
  -- triangle and pentagon).  Mac Lane's triangle and pentagon for Str, and
  -- the strictness witness, come out generically: they are the functorial
  -- images of the spine-level coherences.  No truncation of Obₘ anywhere.
  -- ==========================================================================

  private
    -- Str's path→iso along a List-level path p is Unary's path→iso along
    -- ap ⊗₀ p: the general fact that functors send path→isos to path→isos
    -- (ap-F₀-to-iso), applied to Reindex, whose action on morphisms is the
    -- identity.
    str-bridge : {Γ Δ : List Obₘ} (p : Γ ≡ Δ)
               → path-to {C = Str} p ≡ ≅to (ap ⊗₀ p)
    str-bridge p = sym (ap UMor._≅_.to (RX.ap-F₀-to-iso p))
      where module RX = FB.F-iso Reindex

  module StrPM = from-path-monoid ⊗ᵇ []
    (to-natural-iso record
      { eta     = λ X → U.id
      ; inv     = λ X → U.id
      ; eta∘inv = λ X → U.idl U.id
      ; inv∘eta = λ X → U.idl U.id
      ; natural = λ X Y f → U.idr _ ∙ ⊗ₛ-idl f ∙ sym (U.idl f)
      })
    (to-natural-iso record
      { eta     = λ X → ≅to (ap ⊗₀ (sym (++-idr X)))
      ; inv     = λ X → ≅from (ap ⊗₀ (sym (++-idr X)))
      ; eta∘inv = λ X → ≅invl (ap ⊗₀ (sym (++-idr X)))
      ; inv∘eta = λ X → ≅invr (ap ⊗₀ (sym (++-idr X)))
      ; natural = λ X Y f → unitor-r-nat f
      })
    (to-natural-iso record
      { eta     = λ (Γ , Δ , Ε) → ≅to (ap ⊗₀ (++-assoc Γ Δ Ε))
      ; inv     = λ (Γ , Δ , Ε) → ≅from (ap ⊗₀ (++-assoc Γ Δ Ε))
      ; eta∘inv = λ (Γ , Δ , Ε) → ≅invl (ap ⊗₀ (++-assoc Γ Δ Ε))
      ; inv∘eta = λ (Γ , Δ , Ε) → ≅invr (ap ⊗₀ (++-assoc Γ Δ Ε))
      ; natural = λ x y f →
          ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} h
                      (≅to (ap ⊗₀ (++-assoc (x .fst) (x .snd .fst) (x .snd .snd)))))
             ( ◆≡⊗ₛ (f .fst) (B._◆_ (f .snd .fst) (f .snd .snd))
             ∙ ap (λ h → _⊗ₛ_ {x .fst} {y .fst}
                            {x .snd .fst ++ x .snd .snd} {y .snd .fst ++ y .snd .snd}
                            (f .fst) h)
                  (◆≡⊗ₛ (f .snd .fst) (f .snd .snd)) )
        ∙ assoc-nat {Γ = x .fst} {Δ = x .snd .fst} {Ε = x .snd .snd}
                    {Γ' = y .fst} {Δ' = y .snd .fst} {Ε' = y .snd .snd}
                    (f .fst) (f .snd .fst) (f .snd .snd)
        ∙ ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []}
                      (≅to (ap ⊗₀ (++-assoc (y .fst) (y .snd .fst) (y .snd .snd)))) h)
             (sym ( ◆≡⊗ₛ (B._◆_ (f .fst) (f .snd .fst)) (f .snd .snd)
                  ∙ ap (λ h → _⊗ₛ_ {x .fst ++ x .snd .fst} {y .fst ++ y .snd .fst}
                                 {x .snd .snd} {y .snd .snd} h (f .snd .snd))
                       (◆≡⊗ₛ (f .fst) (f .snd .fst)) ))
      })

  Str-path-monoid : StrPM.Coherent-path-monoid
  Str-path-monoid .StrPM.Coherent-path-monoid.α-path Γ Δ Ε = ++-assoc Γ Δ Ε
  Str-path-monoid .StrPM.Coherent-path-monoid.λ-path Γ     = refl
  Str-path-monoid .StrPM.Coherent-path-monoid.ρ-path Γ     = ++-idr Γ
  Str-path-monoid .StrPM.Coherent-path-monoid.α→-is-path Γ Δ Ε =
    sym (str-bridge (++-assoc Γ Δ Ε))
  Str-path-monoid .StrPM.Coherent-path-monoid.λ←-is-path Γ =
    sym (str-bridge refl ∙ ≅to-refl)
  Str-path-monoid .StrPM.Coherent-path-monoid.ρ←-is-path Γ =
    ≅from-to (ap ⊗₀ (sym (++-idr Γ))) ∙ sym (str-bridge (++-idr Γ))
  Str-path-monoid .StrPM.Coherent-path-monoid.path-triangle Γ Δ =
    ∙-idr (++-assoc Γ [] Δ) ∙ ++-assoc-nil Γ Δ
  Str-path-monoid .StrPM.Coherent-path-monoid.path-pentagon = ++-pentagon→

  Str-monoidal : Monoidal-category Str
  Str-monoidal = StrPM.monoidal Str-path-monoid

  Str-is-strict : is-strict-monoidal Str-monoidal
  Str-is-strict = StrPM.monoidal-is-strict Str-path-monoid
