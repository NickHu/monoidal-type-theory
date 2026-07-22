open import 1Lab.Prelude
open import Cat.Base
open import Cat.Instances.Product
open import Cat.Functor.Closed using (Curry)
open import Cat.Functor.Bifunctor using (Bifunctor)
open import Cat.Functor.Naturality
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso; path→to-∙; path→to-sym)
import Cat.Morphism
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import Multicategory.Unary
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

  -- Structural list-path coherences.  Every list-path reconciliation the
  -- strictification needs is between two paths built ONLY from ++-assoc/++-idr
  -- (refl on elements); they are equal by induction on the spine, for ANY
  -- element type — so `is-set Obₘ` is not needed anywhere below.
  -- (++-assoc-nil, the ++-idr reindex of ++-assoc's empty-middle case, is
  -- imported from Multicategory.)
  private
    -- Naturality of ++-idr against the constant tail [].
    ++-idr-nat : (Γ : List Obₘ) → ap (_++ []) (++-idr Γ) ≡ ++-idr (Γ ++ [])
    ++-idr-nat []      = refl
    ++-idr-nat (a ∷ Γ) = ap (ap (a ∷_)) (++-idr-nat Γ)

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

    -- The associator/unitor triangle at the spine level.
    assoc-idr-mid : (Δ Ε : List Obₘ)
                  → ++-assoc Δ Ε [] ∙ ap (Δ ++_) (++-idr Ε) ≡ ++-idr (Δ ++ Ε)
    assoc-idr-mid []      Ε = ∙-idl (++-idr Ε)
    assoc-idr-mid (a ∷ Δ) Ε = sym (ap-∙ (a ∷_) (++-assoc Δ Ε []) (ap (Δ ++_) (++-idr Ε)))
                            ∙ ap (ap (a ∷_)) (assoc-idr-mid Δ Ε)

    -- ++-idr conjugated by an arbitrary list-path (triangle-style, by J).
    idr-assoc-coh : {V W : List Obₘ} (a : V ≡ W)
                  → (a ∙ sym (++-idr W)) ∙ sym (ap (_++ []) a) ≡ sym (++-idr V)
    idr-assoc-coh {V} = J (λ W a → (a ∙ sym (++-idr W)) ∙ sym (ap (_++ []) a) ≡ sym (++-idr V))
                          (∙-idr (refl ∙ sym (++-idr V)) ∙ ∙-idl (sym (++-idr V)))

    -- Mac Lane's pentagon for the ++-associator, at the spine level.
    ++-pentagon : (A B C D : List Obₘ)
      → ( ap (A ++_) (sym (++-assoc B C D)) ∙ sym (++-assoc A (B ++ C) D) )
          ∙ ap (_++ D) (sym (++-assoc A B C))
        ≡ sym (++-assoc A B (C ++ D)) ∙ sym (++-assoc (A ++ B) C D)
    ++-pentagon []      B C D =
        ap (_∙ refl) (∙-idr (sym (++-assoc B C D)))
      ∙ ∙-idr (sym (++-assoc B C D))
      ∙ sym (∙-idl (sym (++-assoc B C D)))
    ++-pentagon (a ∷ A) B C D =
        ap (_∙ ap (_++ D) (sym (++-assoc (a ∷ A) B C)))
           (sym (ap-∙ (a ∷_) (ap (A ++_) (sym (++-assoc B C D))) (sym (++-assoc A (B ++ C) D))))
      ∙ sym (ap-∙ (a ∷_)
              (ap (A ++_) (sym (++-assoc B C D)) ∙ sym (++-assoc A (B ++ C) D))
              (ap (_++ D) (sym (++-assoc A B C))))
      ∙ ap (ap (a ∷_)) (++-pentagon A B C D)
      ∙ ap-∙ (a ∷_) (sym (++-assoc A B (C ++ D))) (sym (++-assoc (A ++ B) C D))

    -- Coherence used to split a binary restriction (splitμ).
    splitμ-inner : (Δ Ε : List Obₘ)
      → ( ap (_++ []) (sym (ap (Δ ++_) (++-idr Ε))) ∙ ++-assoc Δ (Ε ++ []) [] )
          ∙ ap (Δ ++_) (++-assoc Ε [] [])
        ≡ ++-assoc Δ Ε []
    splitμ-inner [] Ε =
        ap (_∙ ++-assoc Ε [] []) (∙-idr (ap (_++ []) (sym (++-idr Ε))))
      ∙ ap (ap (_++ []) (sym (++-idr Ε)) ∙_) (++-assoc-nil Ε [])
      ∙ sym (ap-∙ (_++ []) (sym (++-idr Ε)) (++-idr Ε))
      ∙ ap (ap (_++ [])) (∙-invl (++-idr Ε))
    splitμ-inner (a ∷ Δ) Ε =
        ap (_∙ ap ((a ∷ Δ) ++_) (++-assoc Ε [] []))
           (sym (ap-∙ (a ∷_)
                   (ap (_++ []) (sym (ap (Δ ++_) (++-idr Ε))))
                   (++-assoc Δ (Ε ++ []) [])))
      ∙ sym (ap-∙ (a ∷_)
              (ap (_++ []) (sym (ap (Δ ++_) (++-idr Ε))) ∙ ++-assoc Δ (Ε ++ []) [])
              (ap (Δ ++_) (++-assoc Ε [] [])))
      ∙ ap (ap (a ∷_)) (splitμ-inner Δ Ε)

    -- Coherence used to split a binary restriction from the left (splitμ-l),
    -- after the fp-loop has been cancelled to refl.
    splitμ-l-inner : (Γ Δ Ε : List Obₘ)
      → ( ( ap (_++ (Ε ++ [])) (sym (ap (Γ ++_) (++-idr Δ)))
              ∙ ++-assoc Γ (Δ ++ []) (Ε ++ []) )
          ∙ ap (Γ ++_) (++-assoc Δ [] (Ε ++ [])) )
          ∙ ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))
        ≡ ap ((Γ ++ Δ) ++_) (++-idr Ε) ∙ ++-assoc Γ Δ Ε
    splitμ-l-inner [] Δ Ε =
        ap (_∙ ap (Δ ++_) (++-idr Ε))
           ( ap (_∙ ++-assoc Δ [] (Ε ++ [])) (∙-idr (ap (_++ (Ε ++ [])) (sym (++-idr Δ))))
           ∙ ap (ap (_++ (Ε ++ [])) (sym (++-idr Δ)) ∙_) (++-assoc-nil Δ (Ε ++ []))
           ∙ sym (ap-∙ (_++ (Ε ++ [])) (sym (++-idr Δ)) (++-idr Δ))
           ∙ ap (ap (_++ (Ε ++ []))) (∙-invl (++-idr Δ)) )
      ∙ ∙-idl (ap (Δ ++_) (++-idr Ε))
      ∙ sym (∙-idr (ap (Δ ++_) (++-idr Ε)))
    splitμ-l-inner (a ∷ Γ) Δ Ε =
        ap (λ z → (z ∙ ap ((a ∷ Γ) ++_) (++-assoc Δ [] (Ε ++ [])))
                     ∙ ap ((a ∷ Γ) ++_) (ap (Δ ++_) (++-idr Ε)))
           (sym (ap-∙ (a ∷_)
                   (ap (_++ (Ε ++ [])) (sym (ap (Γ ++_) (++-idr Δ))))
                   (++-assoc Γ (Δ ++ []) (Ε ++ []))))
      ∙ ap (_∙ ap ((a ∷ Γ) ++_) (ap (Δ ++_) (++-idr Ε)))
           (sym (ap-∙ (a ∷_)
                   (ap (_++ (Ε ++ [])) (sym (ap (Γ ++_) (++-idr Δ))) ∙ ++-assoc Γ (Δ ++ []) (Ε ++ []))
                   (ap (Γ ++_) (++-assoc Δ [] (Ε ++ [])))))
      ∙ sym (ap-∙ (a ∷_)
              (( ap (_++ (Ε ++ [])) (sym (ap (Γ ++_) (++-idr Δ))) ∙ ++-assoc Γ (Δ ++ []) (Ε ++ []) )
                ∙ ap (Γ ++_) (++-assoc Δ [] (Ε ++ [])))
              (ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))))
      ∙ ap (ap (a ∷_)) (splitμ-l-inner Γ Δ Ε)
      ∙ ap-∙ (a ∷_) (ap ((Γ ++ Δ) ++_) (++-idr Ε)) (++-assoc Γ Δ Ε)

  -- Universality, packaged as an equivalence between unary maps out of ⊗Γ and
  -- multimaps out of the context Γ (the ++-idr from `_∘ₘ_` at Θ=Ξ=[] absorbed).
  -- `restrict.injective` is the workhorse: to prove two unary maps ⊗Γ → z equal,
  -- it suffices to compare them after restricting to the generators Γ.
  module _ {Γ : List Obₘ} {z : Obₘ} where
    restrict-equiv : Homₘ (⊗₀ Γ ∷ []) z ≃ Homₘ Γ z
    restrict-equiv =
      ( (λ (φ : Homₘ (⊗₀ Γ ∷ []) z) → _∘ₘ_ {Θ = []} {Ξ = []} φ (⊗-arr Γ))
        , ⊗-arr-univ Γ {Θ = []} {Ξ = []} )
        ∙e path→equiv (ap (λ Ω → Homₘ Ω z) (++-idr Γ))

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

  -- Plugging a subst'd morphism = subst of the plug (naturality of _∘ₘ_ in its
  -- second argument under object-path transport).
  ∘ₘ-substr : {B B' : List Obₘ} {w z : Obₘ}
              (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
            → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) p m)
              ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) p (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  ∘ₘ-substr {B} {B'} {w} {z} a p m =
    J (λ B'' q → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) q m)
                 ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) q (_∘ₘ_ {Θ = []} {Ξ = []} a m))
      (ap (_∘ₘ_ {Θ = []} {Ξ = []} a) (transport-refl m) ∙ sym (transport-refl _))
      p

  -- Substituting the OUTER map's domain-prefix commutes with plugging.
  ∘ₘ-substl : {Θ Θ' Ξ Γ : List Obₘ} {x z : Obₘ}
              (p : Θ ≡ Θ') (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
            → _∘ₘ_ {Θ = Θ'} {Ξ = Ξ} (subst (λ Ω → Homₘ (Ω ++ x ∷ Ξ) z) p f) g
              ≡ subst (λ Ω → Homₘ (Ω ++ Γ ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-substl {Θ} {Θ'} {Ξ} {Γ} {x} {z} p f g =
    J (λ Θ'' q → _∘ₘ_ {Θ = Θ''} {Ξ = Ξ} (subst (λ Ω → Homₘ (Ω ++ x ∷ Ξ) z) q f) g
                 ≡ subst (λ Ω → Homₘ (Ω ++ Γ ++ Ξ) z) q (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g))
      ( ap (λ q → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} q g) (transport-refl f)
      ∙ sym (transport-refl _) )
      p

  -- `restrict` is natural under unary post-composition (assocₘ at the generators).
  restrict-nat : {Γ : List Obₘ} {w z : Obₘ}
                 (a : Homₘ (w ∷ []) z) (φ : Homₘ (⊗₀ Γ ∷ []) w)
               → restrict {Γ} {z} (a U.∘ φ)
                 ≡ subst (λ Ω → Homₘ Ω z) (++-idr Γ)
                     (_∘ₘ_ {Θ = []} {Ξ = []} a (restrict {Γ} {w} φ))
  restrict-nat {Γ} {w} {z} a φ = ap (subst (λ Ω → Homₘ Ω z) (++-idr Γ)) step
    where
      aφ : Homₘ (⊗₀ Γ ∷ []) z
      aφ = _∘ₘ_ {Θ = []} {Ξ = []} a φ
      φσ : Homₘ (Γ ++ []) w
      φσ = _∘ₘ_ {Θ = []} {Ξ = []} φ (⊗-arr Γ)
      Y : Homₘ ((Γ ++ []) ++ []) z
      Y = _∘ₘ_ {Θ = []} {Ξ = []} a φσ
      X : Homₘ (Γ ++ []) z
      X = _∘ₘ_ {Θ = []} {Ξ = []} aφ (⊗-arr Γ)
      -- the assocₘ i0-endpoint (subst over slot-unbury = refl) equals X.
      e0 : _∘ₘ_ {Θ = []} {Ξ = []}
             (subst (λ Ω → Homₘ Ω z) (slot-unbury [] [] (⊗₀ Γ) [] []) aφ) (⊗-arr Γ) ≡ X
      e0 = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q (⊗-arr Γ)) (transport-refl aφ)
      -- the two list-paths (Γ++[])++[] ≡ Γ++[] agree, since List Obₘ is a set.
      path-eq : ++-assoc Γ [] [] ≡ (λ i → [] ++ (++-idr Γ i) ++ [])
      path-eq = ++-assoc-nil Γ []
      pp : PathP (λ i → Homₘ ([] ++ (++-idr Γ i) ++ []) z) Y X
      pp = subst (λ p → PathP (λ i → Homₘ (p i) z) Y X) path-eq
             (symP (assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = []} a φ (⊗-arr Γ)) ▷ e0)
      step : X ≡ _∘ₘ_ {Θ = []} {Ξ = []} a (restrict {Γ} φ)
      step =
        X
          ≡⟨ sym (from-pathp pp) ⟩
        subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) (++-idr Γ) Y
          ≡˘⟨ ∘ₘ-substr a (++-idr Γ) φσ ⟩
        _∘ₘ_ {Θ = []} {Ξ = []} a (restrict {Γ} φ) ∎

  -- Pull `a` past the first universal arrow (front slot, suffix ⊗Δ∷[]).  The
  -- assocₘ boundary is exactly ++-assoc Γ (⊗Δ∷[]) [], so no is-set is needed.
  eqΓ : {Γ Δ : List Obₘ} {w z : Obₘ}
        (a : Homₘ (w ∷ []) z) (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) w)
      → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} a χ) (⊗-arr Γ)
        ≡ subst (λ Ω → Homₘ Ω z) (++-assoc Γ (⊗₀ Δ ∷ []) [])
            (_∘ₘ_ {Θ = []} {Ξ = []} a (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} χ (⊗-arr Γ)))
  eqΓ {Γ} {Δ} {w} {z} a χ =
    sym (from-pathp
      (symP (assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = ⊗₀ Δ ∷ []} a χ (⊗-arr Γ))
        ▷ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ ∷ []} q (⊗-arr Γ))
             (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} a χ))))

  -- Naturality of the two-slot restriction under unary post-composition.  Uses
  -- eqΓ (front pull) + a second assocₘ (whose slot-unbury is exactly eqΓ's
  -- boundary ++-assoc Γ (⊗Δ∷[]) []) + ∘ₘ-substr; is-set only at the end.
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
    ∙ sym (ap (subst (λ Ω → Homₘ Ω z) (++-idr (Γ ++ Δ))) (∘ₘ-substr a P s2))
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
          ∙ sym (from-pathp (symP (assocₘ {Θ = []} {Ξ = []} {Φ = Γ} {Ψ = []}
                                     a s1 (⊗-arr Δ))))

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
      interchange-idl = subst (λ p → PathP (λ i → Homₘ (p i) (⊗₀ Y)) i1' i0') bd
                  (e1 ◁ symP (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = []}
                               {Δ = ⊗₀ X ∷ []} (μ [] Y) (⊗-arr []) f) ▷ e0)
        where
          bd : (λ i → interchangeₘ-boundary {A = Obₘ} [] [] [] (⊗₀ X ∷ []) [] (~ i)) ≡ refl
          bd = refl
          e1 : i1' ≡ _
          e1 = sym (ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ X ∷ []} q (⊗-arr []))
                       (transport-refl _
                         ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ [] ∷ []} {Ξ = []} q f)
                              (transport-refl (μ [] Y))))
          e0 : _ ≡ i0'
          e0 = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q f)
                  (transport-refl (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Y ∷ []} (μ [] Y) (⊗-arr [])))
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
               ( sym (assocₘ (μ Γ'' Δ'') f f')
               ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} q f') (transport-refl μf) )
            ∙ ( sym (assocₘ (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f') g g')
              ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g')
                   (transport-refl (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f') g)) )
          swap : assoc-normalL ≡ assoc-normalR
          swap = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g')
                    (sym (subst (λ p → PathP (λ i → Homₘ (p i) (⊗₀ (Γ'' ++ Δ'')))
                                  assoc-normalR-inner assoc-normalL-inner)
                           bd (e1 ◁ symP (interchangeₘ {Θ = []} {Μ = []} {Κ = []}
                                           {Γ = ⊗₀ Γ ∷ []} {Δ = ⊗₀ Δ' ∷ []} μf f' g) ▷ e0)))
            where
              assoc-normalL-inner : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ' ∷ []) (⊗₀ (Γ'' ++ Δ''))
              assoc-normalL-inner = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []}
                               (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f') g
              assoc-normalR-inner : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ' ∷ []) (⊗₀ (Γ'' ++ Δ''))
              assoc-normalR-inner = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []}
                               (_∘ₘ_ {Θ = ⊗₀ Γ' ∷ []} {Ξ = []} μf g) f'
              bd : (λ i → interchangeₘ-boundary {A = Obₘ} [] (⊗₀ Γ ∷ []) []
                            (⊗₀ Δ' ∷ []) [] (~ i)) ≡ refl
              bd = refl
              e1 : assoc-normalR-inner ≡ _
              e1 = sym (ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} q f')
                           (transport-refl _
                             ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ' ∷ []} {Ξ = []} q g)
                                  (transport-refl μf)))
              e0 : _ ≡ assoc-normalL-inner
              e0 = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g)
                      (transport-refl (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ'' ∷ []} μf f'))
          Rchain : _∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) rhs-comp ≡ assoc-normalR
          Rchain =
              ( sym (assocₘ (f ⊗ₛ g) (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f') g')
              ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g')
                   (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g)
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} (μ Γ' Δ') f'))) )
            ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q g')
                 ( sym (assocₘ (f ⊗ₛ g) (μ Γ' Δ') f')
                 ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} q f')
                      (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} (f ⊗ₛ g) (μ Γ' Δ'))) )
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

  -- Whiskering a path→iso by the identity is again a path→iso (of the whiskered
  -- list-path).  Proven by path induction, bottoming out at ⊗ₛ-id.
  ◀-≅ : {Γ Γ' Δ : List Obₘ} (p : Γ ≡ Γ')
      → _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ} (≅to (ap ⊗₀ p)) U.id ≡ ≅to (ap ⊗₀ (ap (_++ Δ) p))
  ◀-≅ {Γ} {Γ'} {Δ} p =
    J (λ Γ' p → _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ} (≅to (ap ⊗₀ p)) U.id ≡ ≅to (ap ⊗₀ (ap (_++ Δ) p)))
      (ap (λ q → _⊗ₛ_ {Γ} {Γ} {Δ} {Δ} q U.id) ≅to-refl ∙ ⊗ₛ-id Γ Δ ∙ sym ≅to-refl)
      p

  ▶-≅ : {Γ Δ Δ' : List Obₘ} (q : Δ ≡ Δ')
      → _⊗ₛ_ {Γ} {Γ} {Δ} {Δ'} U.id (≅to (ap ⊗₀ q)) ≡ ≅to (ap ⊗₀ (ap (Γ ++_) q))
  ▶-≅ {Γ} {Δ} {Δ'} q =
    J (λ Δ' q → _⊗ₛ_ {Γ} {Γ} {Δ} {Δ'} U.id (≅to (ap ⊗₀ q)) ≡ ≅to (ap ⊗₀ (ap (Γ ++_) q)))
      (ap (λ r → _⊗ₛ_ {Γ} {Γ} {Δ} {Δ} U.id r) ≅to-refl ∙ ⊗ₛ-id Γ Δ ∙ sym ≅to-refl)
      q

  ≅from-refl : {A : Obₘ} → ≅from (refl {x = A}) ≡ U.id
  ≅from-refl = ap UMor._≅_.from (transport-refl UMor.id-iso)

  -- path→iso is a functor: it sends sym to inverse and ∙ to composition.
  ≅from-to : {A B : Obₘ} (p : A ≡ B) → ≅from p ≡ ≅to (sym p)
  ≅from-to p = path→to-sym (Unary M) p

  ≅to-∘ : {A B C : Obₘ} (p : B ≡ C) (q : A ≡ B)
        → ≅to p U.∘ ≅to q ≡ ≅to (q ∙ p)
  ≅to-∘ p q = sym (path→to-∙ (Unary M) q p)

  -- Composing a path→iso onto a multimap transports its codomain.
  ≅to-∘ₘ : {Γ : List Obₘ} {A B : Obₘ} (q : A ≡ B) (m : Homₘ Γ A)
         → _∘ₘ_ {Θ = []} {Ξ = []} (≅to q) m
           ≡ subst (λ z → Homₘ (Γ ++ []) z) q (_∘ₘ_ {Θ = []} {Ξ = []} idₘ m)
  ≅to-∘ₘ {Γ} q m =
    J (λ B q → _∘ₘ_ {Θ = []} {Ξ = []} (≅to q) m
               ≡ subst (λ z → Homₘ (Γ ++ []) z) q (_∘ₘ_ {Θ = []} {Ξ = []} idₘ m))
      ( ap (λ k → _∘ₘ_ {Θ = []} {Ξ = []} k m) ≅to-refl
      ∙ sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} idₘ m)) )
      q

  -- Transport over a 2-variable Homₘ family decomposes into domain then codomain.
  transp-decomp : {X X' : List Obₘ} {A A' : Obₘ}
                  (a : X ≡ X') (b : A ≡ A') (m : Homₘ X A)
                → transport (λ i → Homₘ (a i) (b i)) m
                  ≡ subst (λ z → Homₘ X' z) b (subst (λ Ω → Homₘ Ω A) a m)
  transp-decomp {X} {X'} {A} b0 b m =
    J (λ X' a → transport (λ i → Homₘ (a i) (b i)) m
                ≡ subst (λ z → Homₘ X' z) b (subst (λ Ω → Homₘ Ω A) a m))
      (ap (subst (λ z → Homₘ X z) b) (sym (transport-refl m)))
      b0

  -- Expanding X to X++[] via the unitor iso, then the universal arrow of X,
  -- is the universal arrow of X++[].
  η-arr : (X : List Obₘ)
        → _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr X)))) (⊗-arr X)
          ≡ ⊗-arr (X ++ [])
  -- Remaining: subst (codomain) (idₘ ∘ₘ ⊗-arr X) ≡ ⊗-arr (X ++ []).  This is a
  -- 2-dimensional coherence: idₘr moves the domain X++[]→X, apd ⊗-arr moves both
  -- X→X++[] / ⊗X→⊗(X++[]); the composite (over a domain loop) reconciles to the
  -- codomain-only transport via is-set.
  η-arr X = ≅to-∘ₘ (ap ⊗₀ (sym (++-idr X))) (⊗-arr X)
          ∙ ap (subst (λ z → Homₘ (X ++ []) z) (ap ⊗₀ (sym (++-idr X))))
               (sym (from-pathp (symP (idₘr (⊗-arr X)))))
          ∙ sym (transp-decomp (sym (++-idr X)) (ap ⊗₀ (sym (++-idr X))) (⊗-arr X))
          ∙ from-pathp (apd (λ _ Γ → ⊗-arr Γ) (sym (++-idr X)))

  -- Feeding the unit arrow ⊗-arr [] into μ Y []'s SECOND slot yields the right
  -- unitor iso ηY (mirror of μ-unit-l; via interchange + restrict₂-μ + η-arr).
  μ-unit-r : (Y : List Obₘ)
           → _∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])
             ≡ ≅to (ap ⊗₀ (sym (++-idr Y)))
  μ-unit-r Y = restrict.injective
    ( ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr Y)) swap-eq
    ∙ sym (ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (++-idr Y)) (η-arr Y)) )
    where
      innerc : Homₘ (Y ++ ([] ++ [])) (⊗₀ (Y ++ []))
      innerc = _∘ₘ_ {Θ = Y} {Ξ = []}
                 (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) (⊗-arr Y)) (⊗-arr [])
      swap-eq : _∘ₘ_ {Θ = []} {Ξ = []}
                  (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])) (⊗-arr Y)
                ≡ ⊗-arr (Y ++ [])
      swap-eq =
          e-t
        ∙ sym (from-pathp (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Y} {Δ = []}
                            (μ Y []) (⊗-arr Y) (⊗-arr [])))
        ∙ ( ap (λ h → subst B bd-path (_∘ₘ_ {Θ = Y ++ []} {Ξ = []} h (⊗-arr [])))
               (ap (λ r → subst B r core-YY) slot₁-recon)
          ∙ ap (subst B bd-path) (∘ₘ-substl (sym (++-idr Y)) core-YY (⊗-arr []))
          ∙ sym (subst-∙ B (ap (λ Ω → Ω ++ [] ++ []) (sym (++-idr Y))) bd-path innerc)
          ∙ ap (λ r → subst B r innerc) P-recon
          ∙ restrict₂-μ Y [] )
        where
          B : List Obₘ → Type h
          B = λ Ω → Homₘ Ω (⊗₀ (Y ++ []))
          bd-path : (Y ++ []) ++ [] ++ [] ≡ Y ++ []
          bd-path = interchangeₘ-boundary {A = Obₘ} [] Y [] [] []
          core-YY : Homₘ (Y ++ ⊗₀ [] ∷ []) (⊗₀ (Y ++ []))
          core-YY = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) (⊗-arr Y)
          slot₁-recon : interchange-slot₁ [] Y [] (⊗₀ []) []
                      ≡ ap (_++ ⊗₀ [] ∷ []) (sym (++-idr Y))
          slot₁-recon = ap sym (++-assoc-nil Y (⊗₀ [] ∷ []))
          P-recon : (ap (λ Ω → Ω ++ [] ++ []) (sym (++-idr Y)) ∙ bd-path)
                  ≡ ap (Y ++_) (++-idr [])
          P-recon = ap (λ p → ap (_++ []) (sym (++-idr Y)) ∙ p) (flatten-nil-mid Y [])
                  ∙ sym (ap-∙ (_++ []) (sym (++-idr Y)) (++-idr Y))
                  ∙ ap (ap (_++ [])) (∙-invl (++-idr Y))
          e-t : _∘ₘ_ {Θ = []} {Ξ = []}
                  (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])) (⊗-arr Y) ≡ _
          e-t = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} q (⊗-arr Y))
                   ( ap (λ q → _∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} q (⊗-arr []))
                        (sym (transport-refl (μ Y [])))
                   ∙ sym (transport-refl _) )

  -- Naturality of ⊗-arr under a list-path (by J): the universal arrow of A,
  -- post-composed with the path→iso of q : A ≡ B, is the universal arrow of B.
  arr-nat : {A B : List Obₘ} (q : A ≡ B)
          → _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ q)) (⊗-arr A)
            ≡ subst (λ Ω → Homₘ Ω (⊗₀ B)) (sym (ap (_++ []) q))
                (_∘ₘ_ {Θ = []} {Ξ = []} idₘ (⊗-arr B))
  arr-nat {A} q =
    J (λ B q → _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ q)) (⊗-arr A)
               ≡ subst (λ Ω → Homₘ Ω (⊗₀ B)) (sym (ap (_++ []) q))
                   (_∘ₘ_ {Θ = []} {Ξ = []} idₘ (⊗-arr B)))
      ( ap (λ k → _∘ₘ_ {Θ = []} {Ξ = []} k (⊗-arr A)) ≅to-refl
      ∙ sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} idₘ (⊗-arr A))) )
      q

  -- Restricting the path→iso of q : A ≡ B recovers the universal arrow of B,
  -- reindexed along q (by J; α reindexes ⊗-arr).
  restrict-α : {A B : List Obₘ} (q : A ≡ B)
             → restrict {A} (≅to (ap ⊗₀ q))
               ≡ subst (λ Ω → Homₘ Ω (⊗₀ B)) (sym q) (⊗-arr B)
  restrict-α {A} q =
    J (λ B q → restrict {A} (≅to (ap ⊗₀ q))
               ≡ subst (λ Ω → Homₘ Ω (⊗₀ B)) (sym q) (⊗-arr B))
      (ap (restrict {A}) ≅to-refl ∙ restrict-id A ∙ sym (transport-refl (⊗-arr A)))
      q

  -- expand a, post-composed with the universal arrow, recovers a (reindexed).
  expand-arr : {Ω : List Obₘ} {z : Obₘ} (a : Homₘ Ω z)
             → _∘ₘ_ {Θ = []} {Ξ = []} (expand a) (⊗-arr Ω)
               ≡ subst (λ Ω' → Homₘ Ω' z) (sym (++-idr Ω)) a
  expand-arr {Ω} {z} a =
    sym (from-pathp (symP (to-pathp {A = λ i → Homₘ (++-idr Ω i) z} (restrict.ε a))))

  -- Feeding ⊗-arr[] into μY[]'s second slot past an arbitrary g' collapses (via
  -- interchange + μ-unit-r) to ηY ∘ₘ g'.  Same shape as swap-eq.
  μg-collapse : (Y Δ : List Obₘ) (g' : Homₘ Δ (⊗₀ Y))
              → _∘ₘ_ {Θ = Δ} {Ξ = []}
                  (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) g') (⊗-arr [])
                ≡ _∘ₘ_ {Θ = []} {Ξ = []} (≅to (ap ⊗₀ (sym (++-idr Y)))) g'
  μg-collapse Y Δ g' =
      lhs-recon
    ∙ from-pathp (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Δ} {Δ = []}
                   (μ Y []) g' (⊗-arr []))
    ∙ e-r
    ∙ ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} h g') (μ-unit-r Y)
    where
      B : List Obₘ → Type h
      B = λ Ω → Homₘ Ω (⊗₀ (Y ++ []))
      bd : (Δ ++ []) ++ [] ++ [] ≡ Δ ++ []
      bd = interchangeₘ-boundary {A = Obₘ} [] Δ [] [] []
      μg' : Homₘ (Δ ++ ⊗₀ [] ∷ []) (⊗₀ (Y ++ []))
      μg' = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) g'
      myLHS : Homₘ (Δ ++ ([] ++ [])) (⊗₀ (Y ++ []))
      myLHS = _∘ₘ_ {Θ = Δ} {Ξ = []} μg' (⊗-arr [])
      slot₁-recon : interchange-slot₁ [] Δ [] (⊗₀ []) []
                  ≡ ap (_++ ⊗₀ [] ∷ []) (sym (++-idr Δ))
      slot₁-recon = ap sym (++-assoc-nil Δ (⊗₀ [] ∷ []))
      P-refl : (ap (λ Ω → Ω ++ [] ++ []) (sym (++-idr Δ)) ∙ bd) ≡ refl
      P-refl = ap (λ p → ap (_++ []) (sym (++-idr Δ)) ∙ p) (flatten-nil-mid Δ [])
             ∙ sym (ap-∙ (_++ []) (sym (++-idr Δ)) (++-idr Δ))
             ∙ ap (ap (_++ [])) (∙-invl (++-idr Δ))
      lhs-recon : myLHS
                ≡ subst B bd
                    (_∘ₘ_ {Θ = Δ ++ []} {Ξ = []}
                      (subst B (interchange-slot₁ [] Δ [] (⊗₀ []) []) μg') (⊗-arr []))
      lhs-recon = sym
        ( ap (λ h → subst B bd (_∘ₘ_ {Θ = Δ ++ []} {Ξ = []} h (⊗-arr [])))
             (ap (λ r → subst B r μg') slot₁-recon)
        ∙ ap (subst B bd) (∘ₘ-substl (sym (++-idr Δ)) μg' (⊗-arr []))
        ∙ sym (subst-∙ B (ap (λ Ω → Ω ++ [] ++ []) (sym (++-idr Δ))) bd myLHS)
        ∙ ap (λ r → subst B r myLHS) P-refl
        ∙ transport-refl myLHS )
      e-r : _∘ₘ_ {Θ = []} {Ξ = []}
              (subst B (interchange-slot₂ [] (⊗₀ Y) [] [] [])
                (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []}
                  (subst B (interchange-slot₀ [] (⊗₀ Y) [] (⊗₀ []) []) (μ Y [])) (⊗-arr []))) g'
            ≡ _∘ₘ_ {Θ = []} {Ξ = []}
                (_∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} (μ Y []) (⊗-arr [])) g'
      e-r = ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} h g')
               (transport-refl _
                 ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Y ∷ []} {Ξ = []} q (⊗-arr []))
                      (transport-refl (μ Y [])))

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
      -- which ⊗ₛ-μ rewrites to restrict₂.to(μY[]∘ₘf); `back` collapses that to ηY∘ₘg.
      residual : _∘ₘ_ {Θ = []} {Ξ = []} fid (⊗-arr (X ++ []))
               ≡ _∘ₘ_ {Θ = []} {Ξ = []} ηY (_∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X))
      residual =
          sym (from-pathp (symP (to-pathp {A = λ i → Homₘ (++-idr (X ++ []) i) (⊗₀ (Y ++ []))}
                                          (sym RN'))))
        ∙ ap (subst (λ Ω → Homₘ Ω (⊗₀ (Y ++ []))) (sym (++-idr (X ++ []))))
             (ap restrict₂.to ⊗ₛ-μ-idl)
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
          back = bridge ∙ μg-collapse Y (X ++ []) gX
            where
              B : List Obₘ → Type h
              B = λ Ω → Homₘ Ω (⊗₀ (Y ++ []))
              gX : Homₘ (X ++ []) (⊗₀ Y)
              gX = _∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X)
              μgX : Homₘ ((X ++ []) ++ ⊗₀ [] ∷ []) (⊗₀ (Y ++ []))
              μgX = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} (μ Y []) gX
              target : Homₘ ((X ++ []) ++ ([] ++ [])) (⊗₀ (Y ++ []))
              target = _∘ₘ_ {Θ = X ++ []} {Ξ = []} μgX (⊗-arr [])
              μYf-plugged : Homₘ (X ++ ([] ++ [])) (⊗₀ (Y ++ []))
              μYf-plugged = _∘ₘ_ {Θ = X} {Ξ = []}
                       (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} μYf (⊗-arr X)) (⊗-arr [])
              P0 : X ++ ([] ++ []) ≡ (X ++ []) ++ []
              P0 = ap (X ++_) (++-idr []) ∙ sym (++-idr (X ++ []))
              bd-a : X ++ ⊗₀ [] ∷ [] ≡ (X ++ []) ++ ⊗₀ [] ∷ []
              bd-a = assocₘ-boundary {A = Obₘ} [] [] X [] (⊗₀ [] ∷ [])
              bd-a-recon : sym bd-a ≡ ap (_++ ⊗₀ [] ∷ []) (++-idr X)
              bd-a-recon = ++-assoc-nil X (⊗₀ [] ∷ [])
              comp-refl : (ap (λ Ω → Ω ++ [] ++ []) (++-idr X) ∙ P0) ≡ refl
              comp-refl = ap (λ p → p ∙ P0) (++-idr-nat X)
                        ∙ ap (++-idr (X ++ []) ∙_) (∙-idl (sym (++-idr (X ++ []))))
                        ∙ ∙-invr (++-idr (X ++ []))
              AS : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} μYf (⊗-arr X)
                 ≡ subst B (sym bd-a) μgX
              AS = ap (λ h → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ [] ∷ []} h (⊗-arr X))
                      (sym (transport-refl μYf))
                 ∙ sym (from-pathp (symP (assocₘ {Θ = []} {Ξ = ⊗₀ [] ∷ []} {Φ = []} {Ψ = []}
                                            (μ Y []) f (⊗-arr X))))
              μYf-plugged-eq : μYf-plugged ≡ subst B (ap (λ Ω → Ω ++ [] ++ []) (++-idr X)) target
              μYf-plugged-eq =
                  ap (λ h → _∘ₘ_ {Θ = X} {Ξ = []} h (⊗-arr [])) AS
                ∙ ap (λ h → _∘ₘ_ {Θ = X} {Ξ = []} h (⊗-arr []))
                     (ap (λ r → subst B r μgX) bd-a-recon)
                ∙ ∘ₘ-substl (++-idr X) μgX (⊗-arr [])
              bridge : subst B (sym (++-idr (X ++ []))) (restrict₂.to μYf) ≡ target
              bridge =
                  sym (subst-∙ B (ap (X ++_) (++-idr [])) (sym (++-idr (X ++ []))) μYf-plugged)
                ∙ ap (subst B P0) μYf-plugged-eq
                ∙ sym (subst-∙ B (ap (λ Ω → Ω ++ [] ++ []) (++-idr X)) P0 target)
                ∙ ap (λ r → subst B r target) comp-refl
                ∙ transport-refl target
      inner : _∘ₘ_ {Θ = []} {Ξ = []} fid (restrict {X} ηX)
            ≡ _∘ₘ_ {Θ = []} {Ξ = []} ηY (restrict {X} f)
      inner =
          ap (λ q → _∘ₘ_ {Θ = []} {Ξ = []} fid q)
             (ap (subst (λ Ω → Homₘ Ω (⊗₀ (X ++ []))) (++-idr X)) (η-arr X))
        ∙ ∘ₘ-substr fid (++-idr X) (⊗-arr (X ++ []))
        ∙ ap (subst (λ Ω → Homₘ ([] ++ Ω ++ []) (⊗₀ (Y ++ []))) (++-idr X)) residual
        ∙ sym (∘ₘ-substr ηY (++-idr X) (_∘ₘ_ {Θ = []} {Ξ = []} f (⊗-arr X)))

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
          sym (subst-∙ B (sym (++-idr (Δ ++ Ε))) (++-idr (Δ ++ Ε)) (restrict₂.to {Δ} {Ε} b))
        ∙ ap (λ p → subst B p (restrict₂.to {Δ} {Ε} b))
             (∙-invl (++-idr (Δ ++ Ε)))
        ∙ transport-refl (restrict₂.to {Δ} {Ε} b)

  -- Collapsing μ Δ Ε fed ⊗-arr Ε (slot 2) then ⊗-arr Δ (slot 1) — the reversed
  -- plug order — yields ⊗-arr (Δ ++ Ε), reindexed.  Interchange + restrict₂-μ.
  μ-block : (Δ Ε : List Obₘ)
          → _∘ₘ_ {Θ = []} {Ξ = Ε ++ []}
              (_∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)) (⊗-arr Δ)
            ≡ subst (λ Ω → Homₘ Ω (⊗₀ (Δ ++ Ε))) (sym (ap (Δ ++_) (++-idr Ε))) (⊗-arr (Δ ++ Ε))
  μ-block Δ Ε =
      e-t
    ∙ sym (from-pathp (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Δ} {Δ = Ε}
                        (μ Δ Ε) (⊗-arr Δ) (⊗-arr Ε)))
    ∙ ( ap (λ h → subst B bd-path (_∘ₘ_ {Θ = Δ ++ []} {Ξ = []} h (⊗-arr Ε)))
           (ap (λ r → subst B r core-DE) slot₁-recon)
      ∙ ap (subst B bd-path) (∘ₘ-substl (sym (++-idr Δ)) core-DE (⊗-arr Ε))
      ∙ sym (subst-∙ B (ap (λ Ω → Ω ++ Ε ++ []) (sym (++-idr Δ))) bd-path innerc)
      ∙ ap (λ r → subst B r innerc) P-recon
      ∙ transport-refl innerc
      ∙ innerc≡target )
    where
      B : List Obₘ → Type h
      B = λ Ω → Homₘ Ω (⊗₀ (Δ ++ Ε))
      P : Δ ++ (Ε ++ []) ≡ Δ ++ Ε
      P = ap (Δ ++_) (++-idr Ε)
      bd-path : (Δ ++ []) ++ Ε ++ [] ≡ Δ ++ (Ε ++ [])
      bd-path = interchangeₘ-boundary {A = Obₘ} [] Δ [] Ε []
      core-DE : Homₘ (Δ ++ ⊗₀ Ε ∷ []) (⊗₀ (Δ ++ Ε))
      core-DE = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} (μ Δ Ε) (⊗-arr Δ)
      innerc : Homₘ (Δ ++ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      innerc = _∘ₘ_ {Θ = Δ} {Ξ = []} core-DE (⊗-arr Ε)
      slot₁-recon : interchange-slot₁ [] Δ [] (⊗₀ Ε) [] ≡ ap (_++ ⊗₀ Ε ∷ []) (sym (++-idr Δ))
      slot₁-recon = ap sym (++-assoc-nil Δ (⊗₀ Ε ∷ []))
      P-recon : (ap (λ Ω → Ω ++ Ε ++ []) (sym (++-idr Δ)) ∙ bd-path) ≡ refl
      P-recon = ap (λ p → ap (_++ (Ε ++ [])) (sym (++-idr Δ)) ∙ p) (flatten-nil-mid Δ Ε)
              ∙ sym (ap-∙ (_++ (Ε ++ [])) (sym (++-idr Δ)) (++-idr Δ))
              ∙ ap (ap (_++ (Ε ++ []))) (∙-invl (++-idr Δ))
      subst-cancel-P : subst B (sym P) (subst B P innerc) ≡ innerc
      subst-cancel-P = sym (subst-∙ B P (sym P) innerc)
                     ∙ ap (λ r → subst B r innerc)
                          (∙-invr P)
                     ∙ transport-refl innerc
      innerc≡target : innerc ≡ subst B (sym P) (⊗-arr (Δ ++ Ε))
      innerc≡target = sym subst-cancel-P ∙ ap (subst B (sym P)) (restrict₂-μ Δ Ε)
      e-t : _∘ₘ_ {Θ = []} {Ξ = Ε ++ []}
              (_∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)) (⊗-arr Δ) ≡ _
      e-t = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} q (⊗-arr Δ))
               ( ap (λ q → _∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} q (⊗-arr Ε))
                    (sym (transport-refl (μ Δ Ε)))
               ∙ sym (transport-refl _) )

  -- restrict₃ plugs universal arrows on the DOMAIN, so a codomain post-comp
  -- commutes out as a codomain-subst.
  restrict₃-α : {Γ Δ Ε : List Obₘ} {C C' : Obₘ}
                (q : C ≡ C') (W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) C)
              → restrict₃.to {Γ} {Δ} {Ε} {C'} (_∘ₘ_ {Θ = []} {Ξ = []} (≅to q) W)
                ≡ subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) q (restrict₃.to {Γ} {Δ} {Ε} {C} W)
  restrict₃-α {Γ} {Δ} {Ε} {C} q W =
    J (λ C' q → restrict₃.to {Γ} {Δ} {Ε} {C'} (_∘ₘ_ {Θ = []} {Ξ = []} (≅to q) W)
                ≡ subst (λ z → Homₘ (Γ ++ (Δ ++ Ε)) z) q (restrict₃.to {Γ} {Δ} {Ε} W))
      ( ap (restrict₃.to {Γ} {Δ} {Ε})
           (ap (λ k → _∘ₘ_ {Θ = []} {Ξ = []} k W) ≅to-refl ∙ idₘr W)
      ∙ sym (transport-refl _) )
      q

  -- Generalized ∘ₘ-substr: push a domain-subst of the plugged argument out of
  -- a plug at arbitrary Θ, Ξ.
  ∘ₘ-substrG : {Θ Ξ B B' : List Obₘ} {w z : Obₘ}
               (a : Homₘ (Θ ++ w ∷ Ξ) z) (p : B ≡ B') (m : Homₘ B w)
             → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} a (subst (λ Ω → Homₘ Ω w) p m)
               ≡ subst (λ Ω → Homₘ (Θ ++ Ω ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} a m)
  ∘ₘ-substrG {Θ} {Ξ} {B} {B'} {w} {z} a p m =
    J (λ B'' q → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} a (subst (λ Ω → Homₘ Ω w) q m)
                 ≡ subst (λ Ω → Homₘ (Θ ++ Ω ++ Ξ) z) q (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} a m))
      (ap (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} a) (transport-refl m) ∙ sym (transport-refl _))
      p

  -- Push a suffix-subst of the outer map's domain out of a plug.
  ∘ₘ-subst-suf : {Θ Ξ Ξ' Γ : List Obₘ} {x z : Obₘ}
                 (p : Ξ ≡ Ξ') (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
               → _∘ₘ_ {Θ = Θ} {Ξ = Ξ'} (subst (λ Ω → Homₘ (Θ ++ x ∷ Ω) z) p f) g
                 ≡ subst (λ Ω → Homₘ (Θ ++ Γ ++ Ω) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-subst-suf {Θ} {Ξ} {Ξ'} {Γ} {x} {z} p f g =
    J (λ Ξ'' q → _∘ₘ_ {Θ = Θ} {Ξ = Ξ''} (subst (λ Ω → Homₘ (Θ ++ x ∷ Ω) z) q f) g
                 ≡ subst (λ Ω → Homₘ (Θ ++ Γ ++ Ω) z) q (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g))
      ( ap (λ q → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} q g) (transport-refl f)
      ∙ sym (transport-refl _) )
      p

  -- Split a binary restriction into a ternary one by plugging μ Δ Ε into the
  -- second (merged) slot.
  splitμ : {Γ Δ Ε : List Obₘ} {z : Obₘ} (χ : Homₘ (⊗₀ Γ ∷ ⊗₀ (Δ ++ Ε) ∷ []) z)
         → restrict₂.to {Γ} {Δ ++ Ε} χ
           ≡ restrict₃.to {Γ} {Δ} {Ε} (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ (μ Δ Ε))
  splitμ {Γ} {Δ} {Ε} {z} χ = sym main
    where
      P-DE : Δ ++ (Ε ++ []) ≡ Δ ++ Ε
      P-DE = ap (Δ ++_) (++-idr Ε)
      W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z
      W = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ (μ Δ Ε)
      -- Pull ⊗-arr Ε from outside χ into μ (first assocₘ).
      pullΕ : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)
            ≡ subst (λ Ω → Homₘ Ω z)
                (sym (assocₘ-boundary (⊗₀ Γ ∷ []) (⊗₀ Δ ∷ []) Ε [] []))
                (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ
                  (_∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)))
      pullΕ = sym (from-pathp
        (symP (assocₘ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Φ = ⊗₀ Δ ∷ []} {Ψ = []} {Ρ = Ε}
                 χ (μ Δ Ε) (⊗-arr Ε))
          ▷ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q (⊗-arr Ε))
               (transport-refl W)))
      BΩ : List Obₘ → Type h
      BΩ = λ Ω → Homₘ Ω z
      arrDE : Homₘ (Δ ++ Ε) (⊗₀ (Δ ++ Ε))
      arrDE = ⊗-arr (Δ ++ Ε)
      μEE : Homₘ (⊗₀ Δ ∷ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μEE = _∘ₘ_ {Θ = ⊗₀ Δ ∷ []} {Ξ = []} (μ Δ Ε) (⊗-arr Ε)
      χμEE : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ((Ε ++ []) ++ [])) z
      χμEE = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μEE
      μbb : Homₘ (Δ ++ (Ε ++ [])) (⊗₀ (Δ ++ Ε))
      μbb = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} μEE (⊗-arr Δ)
      χμbb : Homₘ (⊗₀ Γ ∷ ((Δ ++ (Ε ++ [])) ++ [])) z
      χμbb = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ μbb
      χarrDE : Homₘ (⊗₀ Γ ∷ ((Δ ++ Ε) ++ [])) z
      χarrDE = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ arrDE
      χarrG : Homₘ (Γ ++ ⊗₀ (Δ ++ Ε) ∷ []) z
      χarrG = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ (Δ ++ Ε) ∷ []} χ (⊗-arr Γ)
      canon : Homₘ (Γ ++ ((Δ ++ Ε) ++ [])) z
      canon = _∘ₘ_ {Θ = Γ} {Ξ = []} χarrG arrDE
      bd2 : (⊗₀ Γ ∷ []) ++ Δ ++ ((Ε ++ []) ++ []) ≡ (⊗₀ Γ ∷ []) ++ ((([] ++ Δ ++ (Ε ++ [])) ++ []))
      bd2 = assocₘ-boundary (⊗₀ Γ ∷ []) [] Δ (Ε ++ []) []
      icbd : ([] ++ Γ ++ []) ++ (Δ ++ Ε) ++ [] ≡ [] ++ Γ ++ ([] ++ (Δ ++ Ε) ++ [])
      icbd = interchangeₘ-boundary [] Γ [] (Δ ++ Ε) []
      -- Second pull: ⊗-arr Δ into μ.
      pullΔ : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []} χμEE (⊗-arr Δ)
            ≡ subst BΩ (sym bd2) χμbb
      pullΔ = sym (from-pathp
        (symP (assocₘ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Φ = []} {Ψ = Ε ++ []} {Ρ = Δ}
                 χ μEE (⊗-arr Δ))
          ▷ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = (Ε ++ []) ++ []} q (⊗-arr Δ))
               (transport-refl χμEE)))
      -- plugΔ(plugΕ W) rewritten as a single codomain-clean subst of χarrDE.
      stepED : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                 (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ)
             ≡ subst (λ Ω → Homₘ (⊗₀ Γ ∷ Ω) z) (++-assoc Δ Ε []) χarrDE
      stepED =
          ap (λ h → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} h (⊗-arr Δ)) pullΕ
        ∙ ∘ₘ-subst-suf {Θ = ⊗₀ Γ ∷ []} {x = ⊗₀ Δ} (++-assoc Ε [] []) χμEE (⊗-arr Δ)
        ∙ ap (subst (λ Ω → Homₘ (⊗₀ Γ ∷ Δ ++ Ω) z) (++-assoc Ε [] [])) pullΔ
        ∙ ap (λ h → subst (λ Ω → Homₘ (⊗₀ Γ ∷ Δ ++ Ω) z) (++-assoc Ε [] [])
                      (subst BΩ (sym bd2) h))
             ( ap (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ) (μ-block Δ Ε)
             ∙ ∘ₘ-substrG {Θ = ⊗₀ Γ ∷ []} {Ξ = []} χ (sym P-DE) arrDE )
        ∙ ap (subst (λ Ω → Homₘ (⊗₀ Γ ∷ Δ ++ Ω) z) (++-assoc Ε [] []))
             (sym (subst-∙ BΩ (ap (λ Ω → ⊗₀ Γ ∷ (Ω ++ [])) (sym P-DE)) (sym bd2) χarrDE))
        ∙ sym (subst-∙ BΩ (ap (λ Ω → ⊗₀ Γ ∷ (Ω ++ [])) (sym P-DE) ∙ sym bd2)
             (ap (λ Ω → ⊗₀ Γ ∷ Δ ++ Ω) (++-assoc Ε [] [])) χarrDE)
        ∙ ap (λ p → subst BΩ p χarrDE)
             ( ap (_∙ ap (λ Ω → ⊗₀ Γ ∷ Δ ++ Ω) (++-assoc Ε [] []))
                  (sym (ap-∙ (⊗₀ Γ ∷_)
                          (ap (_++ []) (sym P-DE))
                          (++-assoc Δ (Ε ++ []) [])))
             ∙ sym (ap-∙ (⊗₀ Γ ∷_)
                     (ap (_++ []) (sym P-DE) ∙ ++-assoc Δ (Ε ++ []) [])
                     (ap (Δ ++_) (++-assoc Ε [] [])))
             ∙ ap (ap (⊗₀ Γ ∷_)) (splitμ-inner Δ Ε) )
      -- Interchange: swap the plug order of ⊗-arr Γ (slot 1) and ⊗-arr(Δ++Ε).
      swapΓ : _∘ₘ_ {Θ = []} {Ξ = (Δ ++ Ε) ++ []} χarrDE (⊗-arr Γ)
            ≡ subst BΩ (ap (λ Ω → Ω ++ (Δ ++ Ε) ++ []) (sym (++-idr Γ)) ∙ icbd) canon
      swapΓ =
          ap (λ h → _∘ₘ_ {Θ = []} {Ξ = (Δ ++ Ε) ++ []} h (⊗-arr Γ))
             ( ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q arrDE) (sym (transport-refl χ))
             ∙ sym (transport-refl _) )
        ∙ sym (from-pathp (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Γ} {Δ = Δ ++ Ε}
                            χ (⊗-arr Γ) arrDE))
        ∙ ap (λ h → subst BΩ icbd (_∘ₘ_ {Θ = Γ ++ []} {Ξ = []} h arrDE))
             (ap (λ r → subst BΩ r χarrG)
               (ap sym (++-assoc-nil Γ (⊗₀ (Δ ++ Ε) ∷ []))))
        ∙ ap (subst BΩ icbd) (∘ₘ-substl (sym (++-idr Γ)) χarrG arrDE)
        ∙ sym (subst-∙ BΩ (ap (λ Ω → Ω ++ (Δ ++ Ε) ++ []) (sym (++-idr Γ))) icbd canon)
      main : restrict₃.to {Γ} {Δ} {Ε} W ≡ restrict₂.to {Γ} {Δ ++ Ε} χ
      main =
          ap (subst BΩ (ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))))
             ( ap (λ h → _∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])} h (⊗-arr Γ)) stepED
             ∙ ∘ₘ-subst-suf {Θ = []} {x = ⊗₀ Γ} (++-assoc Δ Ε []) χarrDE (⊗-arr Γ)
             ∙ ap (subst (λ Ω → Homₘ (Γ ++ Ω) z) (++-assoc Δ Ε [])) swapΓ )
        ∙ ap (subst BΩ (ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))))
             (sym (subst-∙ BΩ
               (ap (λ Ω → Ω ++ (Δ ++ Ε) ++ []) (sym (++-idr Γ)) ∙ icbd)
               (ap (Γ ++_) (++-assoc Δ Ε [])) canon))
        ∙ sym (subst-∙ BΩ
             ((ap (λ Ω → Ω ++ (Δ ++ Ε) ++ []) (sym (++-idr Γ)) ∙ icbd)
               ∙ ap (Γ ++_) (++-assoc Δ Ε []))
             (ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))) canon)
        ∙ ap (λ p → subst BΩ p canon)
             ( ap (λ z → ((z ∙ ap (Γ ++_) (++-assoc Δ Ε []))
                             ∙ ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))))
                  ( ap (ap (λ Ω → Ω ++ (Δ ++ Ε) ++ []) (sym (++-idr Γ)) ∙_)
                       (flatten-nil-mid Γ (Δ ++ Ε))
                  ∙ sym (ap-∙ (_++ ((Δ ++ Ε) ++ [])) (sym (++-idr Γ)) (++-idr Γ))
                  ∙ ap (ap (_++ ((Δ ++ Ε) ++ []))) (∙-invl (++-idr Γ)) )
             ∙ ap (_∙ ap (Γ ++_) (ap (Δ ++_) (++-idr Ε)))
                  (∙-idl (ap (Γ ++_) (++-assoc Δ Ε [])))
             ∙ sym (ap-∙ (Γ ++_) (++-assoc Δ Ε []) (ap (Δ ++_) (++-idr Ε)))
             ∙ ap (ap (Γ ++_)) (assoc-idr-mid Δ Ε) )

  -- Split a binary restriction into a ternary one by plugging μ Γ Δ into the
  -- FIRST (merged) slot.  Mirror of splitμ: χ's own second slot ⊗Ε is plugged
  -- (Step A interchange) alongside the μ-collapse (μ-block Γ Δ), with a final
  -- interchange reordering the Γ-plug back.
  splitμ-l : {Γ Δ Ε : List Obₘ} {z : Obₘ} (χ : Homₘ (⊗₀ (Γ ++ Δ) ∷ ⊗₀ Ε ∷ []) z)
           → restrict₃.to {Γ} {Δ} {Ε} (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ (μ Γ Δ))
             ≡ subst (λ Ω → Homₘ Ω z) (++-assoc Γ Δ Ε) (restrict₂.to {Γ ++ Δ} {Ε} χ)
  splitμ-l {Γ} {Δ} {Ε} {z} χ =
      ap (subst BΩ P₃) (front-full ∙ flat)
    ∙ sym (subst-∙ BΩ bigpath P₃ canon)
    ∙ ap (λ p → subst BΩ p canon)
         ( ap (λ z → (((z ∙ a3) ∙ a2) ∙ a1) ∙ P₃)
              ( ap (ap (λ Ω → Ω ++ Ε ++ []) (sym (++-idr (Γ ++ Δ))) ∙_)
                   (flatten-nil-mid (Γ ++ Δ) Ε)
              ∙ sym (ap-∙ (_++ (Ε ++ [])) (sym (++-idr (Γ ++ Δ))) (++-idr (Γ ++ Δ)))
              ∙ ap (ap (_++ (Ε ++ []))) (∙-invl (++-idr (Γ ++ Δ))) )
         ∙ ap (λ z → ((z ∙ a2) ∙ a1) ∙ P₃) (∙-idl a3)
         ∙ splitμ-l-inner Γ Δ Ε )
    ∙ subst-∙ BΩ P₂' (++-assoc Γ Δ Ε) canon
    where
      BΩ : List Obₘ → Type h
      BΩ = λ Ω → Homₘ Ω z
      μᵍ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (⊗₀ (Γ ++ Δ))
      μᵍ = μ Γ Δ
      W : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε ∷ []) z
      W = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ μᵍ
      χE : Homₘ (⊗₀ (Γ ++ Δ) ∷ (Ε ++ [])) z
      χE = _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} χ (⊗-arr Ε)
      χEμᵍ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ (Ε ++ [])) z
      χEμᵍ = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μᵍ
      μD : Homₘ (⊗₀ Γ ∷ (Δ ++ [])) (⊗₀ (Γ ++ Δ))
      μD = _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} μᵍ (⊗-arr Δ)
      χEμD : Homₘ (⊗₀ Γ ∷ ((Δ ++ []) ++ (Ε ++ []))) z
      χEμD = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μD
      arrGD : Homₘ (Γ ++ Δ) (⊗₀ (Γ ++ Δ))
      arrGD = ⊗-arr (Γ ++ Δ)
      χEarrGD : Homₘ ((Γ ++ Δ) ++ (Ε ++ [])) z
      χEarrGD = _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE arrGD
      χarrGD-slot : Homₘ ((Γ ++ Δ) ++ ⊗₀ Ε ∷ []) z
      χarrGD-slot = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ arrGD
      canon : Homₘ ((Γ ++ Δ) ++ (Ε ++ [])) z
      canon = _∘ₘ_ {Θ = Γ ++ Δ} {Ξ = []} χarrGD-slot (⊗-arr Ε)
      P₃ : Γ ++ (Δ ++ (Ε ++ [])) ≡ Γ ++ (Δ ++ Ε)
      P₃ = ap (Γ ++_) (ap (Δ ++_) (++-idr Ε))
      P₂' : (Γ ++ Δ) ++ (Ε ++ []) ≡ (Γ ++ Δ) ++ Ε
      P₂' = ap ((Γ ++ Δ) ++_) (++-idr Ε)
      bdD = assocₘ-boundary {A = Obₘ} [] (⊗₀ Γ ∷ []) Δ [] (Ε ++ [])
      bdG = assocₘ-boundary {A = Obₘ} [] [] Γ (Δ ++ []) (Ε ++ [])
      icbdL = interchangeₘ-boundary {A = Obₘ} [] (Γ ++ Δ) [] Ε []
      q-Δ : Γ ++ Δ ≡ Γ ++ (Δ ++ [])
      q-Δ = sym (ap (Γ ++_) (++-idr Δ))
      p' : (Δ ++ []) ++ (Ε ++ []) ≡ Δ ++ (Ε ++ [])
      p' = ++-assoc Δ [] (Ε ++ [])
      fp : (Γ ++ Δ) ++ (Ε ++ []) ≡ (Γ ++ Δ) ++ (Ε ++ [])
      fp = ap (λ Ω → Ω ++ Ε ++ []) (sym (++-idr (Γ ++ Δ))) ∙ icbdL
      a1 = ap (Γ ++_) p'
      a2 = sym bdG
      a3 = ap (λ Ω → Ω ++ Ε ++ []) q-Δ
      a4 = fp
      bigpath = ((a4 ∙ a3) ∙ a2) ∙ a1
      -- Step A: interchange — move ⊗-arr Ε (χ's slot 2) before μ.
      stepA : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)
            ≡ _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE μᵍ
      stepA = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q (⊗-arr Ε)) (sym (transport-refl W))
            ∙ interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Δ = Ε} χ μᵍ (⊗-arr Ε)
            ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} q μᵍ)
                 ( transport-refl _
                 ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} q (⊗-arr Ε)) (transport-refl χ) )
      -- Pull ⊗-arr Δ into μ's second slot (assocₘ).
      pullΔ : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} χEμᵍ (⊗-arr Δ)
            ≡ subst BΩ (sym bdD) χEμD
      pullΔ = sym (from-pathp
        (symP (assocₘ {Θ = []} {Ξ = Ε ++ []} {Φ = ⊗₀ Γ ∷ []} {Ψ = []} {Ρ = Δ} χE μᵍ (⊗-arr Δ))
          ▷ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} q (⊗-arr Δ)) (transport-refl χEμᵍ)))
      -- Pull ⊗-arr Γ into μ's first slot (assocₘ).
      pullΓ : _∘ₘ_ {Θ = []} {Ξ = (Δ ++ []) ++ (Ε ++ [])} χEμD (⊗-arr Γ)
            ≡ subst BΩ (sym bdG)
                (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE (_∘ₘ_ {Θ = []} {Ξ = Δ ++ []} μD (⊗-arr Γ)))
      pullΓ = sym (from-pathp
        (symP (assocₘ {Θ = []} {Ξ = Ε ++ []} {Φ = []} {Ψ = Δ ++ []} {Ρ = Γ} χE μD (⊗-arr Γ))
          ▷ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = (Δ ++ []) ++ (Ε ++ [])} q (⊗-arr Γ)) (transport-refl χEμD)))
      -- Final interchange: reorder ⊗-arr(Γ++Δ) (slot 1) before ⊗-arr Ε (slot 2).
      finalIC : χEarrGD ≡ subst BΩ fp canon
      finalIC =
          ap (λ h → _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} h arrGD)
             ( ap (λ q → _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} q (⊗-arr Ε)) (sym (transport-refl χ))
             ∙ sym (transport-refl _) )
        ∙ sym (from-pathp (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = Γ ++ Δ} {Δ = Ε}
                            χ arrGD (⊗-arr Ε)))
        ∙ ap (λ h → subst BΩ icbdL (_∘ₘ_ {Θ = (Γ ++ Δ) ++ []} {Ξ = []} h (⊗-arr Ε)))
             (ap (λ r → subst BΩ r χarrGD-slot)
               (ap sym (++-assoc-nil (Γ ++ Δ) (⊗₀ Ε ∷ []))))
        ∙ ap (subst BΩ icbdL) (∘ₘ-substl (sym (++-idr (Γ ++ Δ))) χarrGD-slot (⊗-arr Ε))
        ∙ sym (subst-∙ BΩ (ap (λ Ω → Ω ++ Ε ++ []) (sym (++-idr (Γ ++ Δ)))) icbdL canon)
      -- Collapse (μ Γ Δ ∘ arr Δ) ∘ arr Γ via μ-block, then finalIC.
      collapse : _∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE (_∘ₘ_ {Θ = []} {Ξ = Δ ++ []} μD (⊗-arr Γ))
               ≡ subst (λ Ω → Homₘ (Ω ++ Ε ++ []) z) q-Δ (subst BΩ fp canon)
      collapse = ap (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE) (μ-block Γ Δ)
               ∙ ∘ₘ-substrG {Θ = []} {Ξ = Ε ++ []} χE q-Δ arrGD
               ∙ ap (subst (λ Ω → Homₘ (Ω ++ Ε ++ []) z) q-Δ) finalIC
      -- Assemble the inner ternary term.
      front : _∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
                (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                  (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ)) (⊗-arr Γ)
            ≡ subst (λ Ω → Homₘ (Γ ++ Ω) z) p'
                (subst BΩ (sym bdG)
                  (_∘ₘ_ {Θ = []} {Ξ = Ε ++ []} χE (_∘ₘ_ {Θ = []} {Ξ = Δ ++ []} μD (⊗-arr Γ))))
      front =
          ap (λ h → _∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])} h (⊗-arr Γ))
             ( ap (λ h → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []} h (⊗-arr Δ)) stepA
             ∙ pullΔ )
        ∙ ∘ₘ-subst-suf {Θ = []} {Ξ = (Δ ++ []) ++ (Ε ++ [])} {Ξ' = Δ ++ (Ε ++ [])} {Γ = Γ} {x = ⊗₀ Γ}
             p' χEμD (⊗-arr Γ)
        ∙ ap (subst (λ Ω → Homₘ (Γ ++ Ω) z) p') pullΓ
      front-full : _∘ₘ_ {Θ = []} {Ξ = Δ ++ (Ε ++ [])}
                     (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = Ε ++ []}
                       (_∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} W (⊗-arr Ε)) (⊗-arr Δ)) (⊗-arr Γ)
                 ≡ subst (λ Ω → Homₘ (Γ ++ Ω) z) p'
                     (subst BΩ (sym bdG)
                       (subst (λ Ω → Homₘ (Ω ++ Ε ++ []) z) q-Δ (subst BΩ fp canon)))
      front-full = front
                 ∙ ap (λ t → subst (λ Ω → Homₘ (Γ ++ Ω) z) p' (subst BΩ (sym bdG) t)) collapse
      flat : subst (λ Ω → Homₘ (Γ ++ Ω) z) p'
               (subst BΩ (sym bdG) (subst (λ Ω → Homₘ (Ω ++ Ε ++ []) z) q-Δ (subst BΩ fp canon)))
           ≡ subst BΩ bigpath canon
      flat = ap (subst BΩ a1)
                ( ap (subst BΩ a2) (sym (subst-∙ BΩ a4 a3 canon))
                ∙ sym (subst-∙ BΩ (a4 ∙ a3) a2 canon) )
           ∙ sym (subst-∙ BΩ ((a4 ∙ a3) ∙ a2) a1 canon)

  -- Domain-subst and codomain-subst of a Homₘ commute (independent indices).
  subst-dom-cod : {X X' : List Obₘ} {A A' : Obₘ} (p : X ≡ X') (q : A ≡ A') (m : Homₘ X A)
    → subst (λ Ω → Homₘ Ω A') p (subst (λ z → Homₘ X z) q m)
      ≡ subst (λ z → Homₘ X' z) q (subst (λ Ω → Homₘ Ω A) p m)
  subst-dom-cod {X} {X'} {A} {A'} p q m =
    J (λ X' p → subst (λ Ω → Homₘ Ω A') p (subst (λ z → Homₘ X z) q m)
                ≡ subst (λ z → Homₘ X' z) q (subst (λ Ω → Homₘ Ω A) p m))
      (transport-refl _ ∙ ap (subst (λ z → Homₘ X z) q) (sym (transport-refl m)))
      p

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
          ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q (μ Δ Ε)) (sym (transport-refl χ-A))
        ∙ assocₘ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Φ = []} {Ψ = []}
            a-A (_⊗ₛ_ {Δ} {Δ'} {Ε} {Ε'} f₂ f₃) (μ Δ Ε)
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
      aBμ : Homₘ (⊗₀ Γ ∷ ⊗₀ Δ ∷ ⊗₀ Ε' ∷ []) (⊗₀ ((Γ' ++ Δ') ++ Ε'))
      aBμ = _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} a-B (μ Γ Δ)
      WB3-eq : _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} χ-B (μ Γ Δ) ≡ WB3
      WB3-eq =
          ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε ∷ []} q (μ Γ Δ))
             (sym (transport-refl _
                  ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ (Γ ++ Δ) ∷ []} {Ξ = []} q f₃) (transport-refl a-B)))
        ∙ sym (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Δ = ⊗₀ Ε ∷ []}
                a-B (μ Γ Δ) f₃)
        ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃)
             ( transport-refl aBμ
             ∙ ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} q (μ Γ Δ)) (sym (transport-refl a-B))
             ∙ assocₘ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} {Φ = []} {Ψ = []} {Ρ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []}
                 μGD' f12 (μ Γ Δ)
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
          step1 =
              ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} q f₁)
                 (sym (transport-refl _
                      ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ' ∷ []} {Ξ = []} q (μ Δ' Ε'))
                           (transport-refl (μ Γ' (Δ' ++ Ε')))))
            ∙ sym (interchangeₘ {Θ = []} {Μ = []} {Κ = []} {Γ = ⊗₀ Γ ∷ []} {Δ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []}
                    (μ Γ' (Δ' ++ Ε')) f₁ (μ Δ' Ε'))
            ∙ ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} q (μ Δ' Ε')) (transport-refl a-A)
          step2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A (μ Δ' Ε')) f₂
                ≡ _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A μΔ'f₂
          step2 =
              ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂)
                 (sym (transport-refl (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A (μ Δ' Ε'))))
            ∙ assocₘ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Φ = []} {Ψ = ⊗₀ Ε' ∷ []} {Ρ = ⊗₀ Δ ∷ []}
                a-A (μ Δ' Ε') f₂
          step3 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []}
                    (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A μΔ'f₂) f₃
                ≡ WA3
          step3 =
              ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃)
                 (sym (transport-refl (_∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} a-A μΔ'f₂)))
            ∙ assocₘ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Φ = ⊗₀ Δ ∷ []} {Ψ = []} {Ρ = ⊗₀ Ε ∷ []}
                a-A μΔ'f₂ f₃

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
          tstep1 =
              ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} q f₁) (sym (transport-refl MB'))
            ∙ assocₘ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} {Φ = []} {Ψ = ⊗₀ Δ' ∷ []} {Ρ = ⊗₀ Γ ∷ []}
                μGD' (μ Γ' Δ') f₁
          tstep2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []}
                     (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' μΓ'f₁) f₂
                 ≡ b1
          tstep2 =
              ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂)
                 (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} μGD' μΓ'f₁)))
            ∙ assocₘ {Θ = []} {Ξ = ⊗₀ Ε' ∷ []} {Φ = ⊗₀ Γ ∷ []} {Ψ = []} {Ρ = ⊗₀ Δ ∷ []}
                μGD' μΓ'f₁ f₂

      -- α' (codomain iso) commutes past the three domain f-plugs (3 assocₘ).
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
          cstep1 = ap (λ q → _∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} q f₁)
                      (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} α' MB')))
                 ∙ assocₘ {Θ = []} {Ξ = []} {Φ = []} {Ψ = ⊗₀ Δ' ∷ ⊗₀ Ε' ∷ []} {Ρ = ⊗₀ Γ ∷ []}
                     α' MB' f₁
          cstep2 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁) f₂
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁f₂
          cstep2 = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = ⊗₀ Ε' ∷ []} q f₂)
                      (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁)))
                 ∙ assocₘ {Θ = []} {Ξ = []} {Φ = ⊗₀ Γ ∷ []} {Ψ = ⊗₀ Ε' ∷ []} {Ρ = ⊗₀ Δ ∷ []}
                     α' MBf₁ f₂
          cstep3 : _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁f₂) f₃
                 ≡ _∘ₘ_ {Θ = []} {Ξ = []} α' T3MB'
          cstep3 = ap (λ q → _∘ₘ_ {Θ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ξ = []} q f₃)
                      (sym (transport-refl (_∘ₘ_ {Θ = []} {Ξ = []} α' MBf₁f₂)))
                 ∙ assocₘ {Θ = []} {Ξ = []} {Φ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {Ψ = []} {Ρ = ⊗₀ Ε ∷ []}
                     α' MBf₁f₂ f₃

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
        ∙ ∘ₘ-substr FA (sym (++-assoc Γ Δ Ε)) (⊗-arr (Γ ++ (Δ ++ Ε)))
        ∙ ap (subst (λ Ω → Homₘ ([] ++ Ω ++ []) (⊗₀ (Γ' ++ Δ' ++ Ε'))) (sym (++-assoc Γ Δ Ε)))
             (expand-arr aFA)
        ∙ μ-hex-f
        ∙ sym (ap (λ h → _∘ₘ_ {Θ = []} {Ξ = []} α' h) (restrict.ε aFB))

  -- The Monoidal `_◀_`/`_▶_` are our tensor-of-morphisms whiskered by identity.
  ◀-bridge : {Γ Γ' Δ : List Obₘ} (X : U.Hom (⊗₀ Γ) (⊗₀ Γ'))
           → (X B.◀ Δ) ≡ _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ} X U.id
  ◀-bridge X = refl

  ▶-bridge : {Γ Δ Δ' : List Obₘ} (Y : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
           → (Γ B.▶ Y) ≡ _⊗ₛ_ {Γ} {Γ} {Δ} {Δ'} U.id Y
  ▶-bridge Y = refl

  -- The bifunctor's pair action (f ◆ g = (f ◀ _) ∘ (_ ▶ g)) is our ⊗ₛ.
  ◆≡⊗ₛ : {Γ Γ' Δ Δ' : List Obₘ}
         (f : U.Hom (⊗₀ Γ) (⊗₀ Γ')) (g : U.Hom (⊗₀ Δ) (⊗₀ Δ'))
       → B._◆_ f g ≡ _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g
  ◆≡⊗ₛ {Γ} {Γ'} {Δ} {Δ'} f g =
      sym (⊗ₛ-∘ f U.id U.id g)
    ∙ ap₂ (λ a b → _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} a b) (U.idr f) (U.idl g)

  -- The strict monoidal structure.  Objects are lists, tensor is concatenation,
  -- Unit is [].  Left unit is definitional ([] ++ X = X); right unit and the
  -- associator are the `path→iso`s of the corresponding list-path.
  Str-monoidal : Monoidal-category Str
  Str-monoidal .Monoidal-category.-⊗-  = ⊗ᵇ
  Str-monoidal .Monoidal-category.Unit = []
  Str-monoidal .Monoidal-category.unitor-l = to-natural-iso record
    { eta     = λ X → U.id
    ; inv     = λ X → U.id
    ; eta∘inv = λ X → U.idl U.id
    ; inv∘eta = λ X → U.idl U.id
    ; natural = λ X Y f → U.idr _ ∙ ⊗ₛ-idl f ∙ sym (U.idl f)
    }
  Str-monoidal .Monoidal-category.unitor-r = to-natural-iso record
    { eta     = λ X → ≅to (ap ⊗₀ (sym (++-idr X)))
    ; inv     = λ X → ≅from (ap ⊗₀ (sym (++-idr X)))
    ; eta∘inv = λ X → ≅invl (ap ⊗₀ (sym (++-idr X)))
    ; inv∘eta = λ X → ≅invr (ap ⊗₀ (sym (++-idr X)))
    ; natural = λ X Y f → unitor-r-nat f
    }
  Str-monoidal .Monoidal-category.associator = to-natural-iso record
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
    }
  Str-monoidal .Monoidal-category.triangle {A} {B} =
      ap (λ a → a U.∘ ≅from (ap ⊗₀ (++-assoc A [] B)))
         ( ap (λ r → _⊗ₛ_ {A ++ []} {A} {B} {B} r U.id)
              (≅from-to (ap ⊗₀ (sym (++-idr A))))
         ∙ ◀-≅ {A ++ []} {A} {B} (++-idr A) )
    ∙ ap (λ b → ≅to (ap ⊗₀ (ap (_++ B) (++-idr A))) U.∘ b)
         (≅from-to (ap ⊗₀ (++-assoc A [] B)))
    ∙ ≅to-∘ (ap ⊗₀ (ap (_++ B) (++-idr A))) (ap ⊗₀ (sym (++-assoc A [] B)))
    ∙ ap ≅to ( sym (ap-∙ ⊗₀ (sym (++-assoc A [] B)) (ap (_++ B) (++-idr A)))
             ∙ ap (ap ⊗₀)
                  ( ap (λ r → sym r ∙ ap (_++ B) (++-idr A)) (++-assoc-nil A B)
                  ∙ ∙-invl (ap (_++ B) (++-idr A)) ) )
    ∙ sym (⊗ₛ-id A B ∙ sym ≅to-refl)
  Str-monoidal .Monoidal-category.pentagon {A} {B} {C} {D} =
      ap (λ a → a U.∘ (aBCD U.∘ aA-BCD))
         ( ap (λ r → _⊗ₛ_ {A ++ (B ++ C)} {(A ++ B) ++ C} {D} {D} r U.id)
              (≅from-to (ap ⊗₀ (++-assoc A B C)))
         ∙ ◀-≅ {A ++ (B ++ C)} {(A ++ B) ++ C} {D} (sym (++-assoc A B C)) )
    ∙ ap (λ b → ≅to P1 U.∘ (b U.∘ aA-BCD)) (≅from-to (ap ⊗₀ (++-assoc A (B ++ C) D)))
    ∙ ap (λ c → ≅to P1 U.∘ (≅to P2 U.∘ c))
         ( ap (λ r → _⊗ₛ_ {A} {A} {B ++ (C ++ D)} {(B ++ C) ++ D} U.id r)
              (≅from-to (ap ⊗₀ (++-assoc B C D)))
         ∙ ▶-≅ {A} {B ++ (C ++ D)} {(B ++ C) ++ D} (sym (++-assoc B C D)) )
    ∙ ap (λ x → ≅to P1 U.∘ x) (≅to-∘ P2 P3)
    ∙ ≅to-∘ P1 (P3 ∙ P2)
    ∙ ap ≅to
        ( ap (_∙ P1) (sym (ap-∙ ⊗₀ (ap (A ++_) (sym (++-assoc B C D)))
                                   (sym (++-assoc A (B ++ C) D))))
        ∙ sym (ap-∙ ⊗₀ (ap (A ++_) (sym (++-assoc B C D)) ∙ sym (++-assoc A (B ++ C) D))
                       (ap (_++ D) (sym (++-assoc A B C))))
        ∙ ap (ap ⊗₀) (++-pentagon A B C D)
        ∙ ap-∙ ⊗₀ (sym (++-assoc A B (C ++ D))) (sym (++-assoc (A ++ B) C D)) )
    ∙ sym ( ap (λ a → a U.∘ ≅from (ap ⊗₀ (++-assoc A B (C ++ D))))
               (≅from-to (ap ⊗₀ (++-assoc (A ++ B) C D)))
          ∙ ap (λ b → ≅to Q1 U.∘ b) (≅from-to (ap ⊗₀ (++-assoc A B (C ++ D))))
          ∙ ≅to-∘ Q1 Q2 )
    where
      aBCD  = ≅from (ap ⊗₀ (++-assoc A (B ++ C) D))
      aA-BCD = _⊗ₛ_ {A} {A} {B ++ (C ++ D)} {(B ++ C) ++ D} U.id
                    (≅from (ap ⊗₀ (++-assoc B C D)))
      P1 = ap ⊗₀ (ap (_++ D) (sym (++-assoc A B C)))
      P2 = ap ⊗₀ (sym (++-assoc A (B ++ C) D))
      P3 = ap ⊗₀ (ap (A ++_) (sym (++-assoc B C D)))
      Q1 = ap ⊗₀ (sym (++-assoc (A ++ B) C D))
      Q2 = ap ⊗₀ (sym (++-assoc A B (C ++ D)))
