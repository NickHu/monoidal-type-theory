open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso ; Hom-transport)
open import Cat.Functor.Naturality
import Cat.Monoidal.Reasoning as MonR
import Cat.Bi.Reasoning
open import Cat.Functor.Properties
open import Cat.Functor.Equivalence
open import Cat.Functor.Bifunctor using (Bifunctor ; biiso→isoⁿ)
open import Cat.Functor.Compose using (precompose₂ ; postcompose₂)
import Cat.Monoidal.Functor as MonF
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import Multicategory.Unary
open import Multicategory.Instances.Monoidal
open import Monoidal.Strict using (is-strict-monoidal)
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict
import Multicategory.Strictification.Equivalence as StrEq

-- The coherence theorem for monoidal categories: every monoidal category C is
-- monoidally equivalent to a strict one.  The file culminates in the packaged
-- statement `monoidal-strictification`: there is a strict monoidal category
-- (`Str`, `Str-monoidal`, the strictification of the representable
-- multicategory of C) and a strong monoidal functor `Comparison : Str → C`
-- whose underlying functor is an equivalence of categories.
--
-- The comparison functor factors through the general (multicategory-level)
-- equivalence of Multicategory.Strictification.Equivalence:
--
--   Str --Reindex--> Unary Mᵣ --Unwrap--> C
--
-- so it sends a context Γ to its tensor ⊗-context Γ and a strict morphism
-- f : (⊗Γ ⊗ Unit) → ⊗Δ to `f ∘ ρ→` : ⊗Γ → ⊗Δ.  The key computation is that
-- the multicategory composition, at singleton contexts, reduces to plain
-- composition conjugated by the right unitor:
--   plug [] (a ∷ []) [] m = ρ→ b ∘ m ,
-- so `Unwrap`'s compositionality is pure associativity, and it is fully
-- faithful (precomposition with the unitor iso ρ→) and split essentially
-- surjective on the nose; the monoidal structure on the composite is built
-- from the μ ↔ φ bridge (`bundle`/`compute`/`μ-φ`) below.
module Multicategory.Instances.Monoidal.Coherence
  {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where

  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using
    (⊗-context ; plug ; plug-nil ; plug-cons ; plug-id ; Piso ; ⊗-context-++
    ; ⊗-context-++-idr ; ⊗-context-++-idr-path ; ⊗-context-++-[]-ρ ; path→iso-ap-⊗
    ; path→iso-refl ; φ ; ++-assoc-⊗-iso ; ++-assoc-⊗-path ; F-α→)

  private
    Mᵣ : Premulticategory o h
    Mᵣ = monoidal→multicategory C M₀

    rep : Rep.is-representable Mᵣ
    rep = monoidal→multicategory-is-representable C M₀

  open Premulticategory Mᵣ using (_∘ₘ_ ; idₘ)
  open Strict Mᵣ rep using
    (Str ; ⊗₀ ; ⊗-arr ; μ ; _⊗ₛ_ ; ⊗ₛ-μ ; restrict₂-equiv ; restrict₂-μ ; Str-monoidal
    ; Str-is-strict ; ≅to ; ≅to-refl ; ≅from-to)
  open StrEq Mᵣ rep using (Reindex ; Reindex-is-equivalence)

  private module MR = MonR M₀

  -- `import` (not `open import`): the parameterised module's λ≅/ρ≅ would clash
  -- with Monoidal-category's, so only the triangle coherence is brought in.
  open Cat.Bi.Reasoning (Deloop M₀) using (triangle-inv)


  -- The `.to` of the unit-appending iso factors as ρ→ after the ++[] reindex:
  -- (⊗-context-++ Γ []).to = ρ→ (⊗Γ) ∘ (⊗-context-++-idr Γ).to.  This is the
  -- workhorse form of `⊗-context-++-[]-ρ`, shared by `plug-sing`, `bundle`,
  -- `plug-tail` and `ρ←-reindex` below.
  ++[]-to-ρ→ : (Γ : List Ob)
    → (⊗-context-++ Γ []) .to ≡ ρ→ (⊗-context Γ) ∘ (⊗-context-++-idr Γ) .to
  ++[]-to-ρ→ Γ = intror (⊗-context-++-idr Γ .invr) ∙ pulll (⊗-context-++-[]-ρ Γ)

  -- Singleton plug = right-unitor conjugation.  Uses `plug-nil`, the identity
  -- `(⊗-context-++ (a∷[]) []).to = ρ→ (a ⊗ Unit)` (from ++[]-to-ρ→, whose
  -- ++-idr factor is `a ▶ id = id`), and naturality of ρ→.
  plug-sing : (a b : Ob) (m : Hom (a ⊗ Unit) b)
    → plug [] (a ∷ []) [] m ≡ ρ→ b ∘ m
  plug-sing a b m =
      plug-nil (a ∷ []) [] m
    ∙ ap ((m ◀ Unit) ∘_) (++[]-to-ρ→ (a ∷ []) ∙ elimr ▶.F-id)
    ∙ sym (MR.ρ→nat m)

  -- The monoidal-specific half of the comparison: Unary Mᵣ ≃ C by unwrapping
  -- the unit (F₀ = identity on objects, F₁ = precompose ρ→; compositionality
  -- is `plug-sing` + associativity).
  Unwrap : Functor (Unary Mᵣ) C
  Unwrap .Functor.F₀ x     = x
  Unwrap .Functor.F₁ {x} m = m ∘ ρ→ x
  Unwrap .Functor.F-id     = ρ≅ .invr
  Unwrap .Functor.F-∘ {x} g f =
      ap (_∘ ρ→ x) (ap (g ∘_) (plug-sing x _ f))
    ∙ pullr (sym (assoc _ _ _))
    ∙ assoc _ _ _

  -- Fully faithful (precomposition with the iso ρ→) and split eso (on the
  -- nose): an equivalence.
  Unwrap-is-equivalence : is-equivalence Unwrap
  Unwrap-is-equivalence = ff+split-eso→is-equivalence
    (λ {x} {y} → invertible-precomp-equiv (iso→invertible (ρ≅ {x})))
    (λ y → y , id-iso)

  -- The comparison functor Str → C factors through the general (multicategory-
  -- level) comparison of Multicategory.Strictification.Equivalence:
  --
  --   Str --Reindex--> Unary Mᵣ --Unwrap--> C
  --
  -- On objects and morphisms the composite still reduces definitionally to
  -- Γ ↦ ⊗-context Γ and f ↦ f ∘ ρ→ (⊗-context Γ), so everything below can
  -- compute through it as if it were defined directly.
  Comparison : Functor Str C
  Comparison = Unwrap F∘ Reindex

  -- Fully faithful: the hom-action is precomposition with the iso ρ→ (⊗Γ).
  Comparison-ff : is-fully-faithful Comparison
  Comparison-ff {Γ} {Δ} = invertible-precomp-equiv (iso→invertible (ρ≅ {⊗-context Γ}))

  -- Split essentially surjective: c is hit by the singleton context (c ∷ []),
  -- since ⊗-context (c ∷ []) = c ⊗ Unit ≅ c (inverse right unitor).
  Comparison-eso : is-split-eso Comparison
  Comparison-eso c = (c ∷ []) , (ρ≅ {c} Iso⁻¹)

  -- Hence Str and C have equivalent underlying categories: C ≃ C^str.  The
  -- equivalence is the composite of the two equivalences above.
  Comparison-is-equivalence : is-equivalence Comparison
  Comparison-is-equivalence =
    is-equivalence-∘ Unwrap-is-equivalence Reindex-is-equivalence

  -- ==========================================================================
  -- Monoidal structure ingredients (toward `Monoidal-functor-on Comparison`).
  -- ==========================================================================

  -- The comparison map φ Γ Δ = (⊗-context-++ Γ Δ).from : ⊗Γ ⊗ ⊗Δ → ⊗(Γ++Δ) is
  -- invertible (it is one leg of the ⊗-context-++ iso).  This is the F-mult-inv
  -- ingredient of the strong monoidal structure.
  φ-inv : (Γ Δ : List Ob) → is-invertible (φ Γ Δ)
  φ-inv Γ Δ = iso→invertible (⊗-context-++ Γ Δ Iso⁻¹)

  -- Bundling coherence (the heart of the μ ↔ φ bridge).  `restrict₂.to` of the
  -- unit-adjusted φ reduces, via `⊗-arr = id`, to two `plug _ _ _ id` legs.
  -- Rewriting both legs with `plug-id` upfront (they are the isos `Piso`) leaves
  -- the *pure-iso* coherence `bundle-core`: no `plug` in sight, and every
  -- constituent (⊗-context-++, Piso, φ) is structural, so both cases of the
  -- Γ-induction reduce definitionally — cons is α-mid + an α≅ cancellation +
  -- ▶.F-∘ folds, and the base collapses via λ→-naturality + `++[]-to-ρ→`.
  -- Associator naturality in the third slot (whiskering h): α→ slides a
  -- whiskered map from (a⊗b)▶h to a▶(b▶h).
  α-mid : (a b : Ob) {X Y : Ob} (h : Hom X Y)
    → α→ (a , b , Y) ∘ ((a ⊗ b) ▶ h) ≡ (a ▶ (b ▶ h)) ∘ α→ (a , b , X)
  α-mid a b {X} {Y} h = MR.▶-assoc {f = a} {g = b} .Isoⁿ.to .is-natural X Y h

  private
    bundle-core : (Γ Δ : List Ob)
      → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
          ∘ (⊗-context-++ Γ (⊗₀ Δ ∷ [])) .to) ∘ Piso Γ Δ [] .to
        ≡ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .to
    bundle-core [] Δ =
        ap (_∘ (⊗-context-++ Δ []) .to)
           (pullr (sym (MR.λ→nat (ρ← D))) ∙ cancell (λ≅ .invr))
      ∙ ap (ρ← D ∘_) (++[]-to-ρ→ Δ)
      ∙ cancell (ρ≅ .invr)
      ∙ ap (λ i → i .to) (sym (⊗-context-++-idr-path Δ))
      where D = ⊗-context Δ
    bundle-core (a ∷ Γ) Δ =
        ap (_∘ (a ▶ Piso Γ Δ [] .to))
           ( ap (_∘ (α← _ ∘ (a ▶ ψ .to))) (pullr (α-mid a (⊗-context Γ) (ρ← D)))
           ∙ pullr (pullr (cancell (α≅ .invl)))
           ∙ ap ((a ▶ φ Γ Δ) ∘_) (sym (▶.F-∘ _ _))
           ∙ sym (▶.F-∘ _ _) )
      ∙ sym (▶.F-∘ _ _)
      ∙ ap (a ▶_) (ap (_∘ Piso Γ Δ [] .to) (assoc _ _ _) ∙ bundle-core Γ Δ)
      ∙ ap (λ i → i .to) (sym (path→iso-ap-⊗ a (ap ⊗-context (ap (Γ ++_) (++-idr Δ)))))
      where
        D = ⊗-context Δ
        ψ = ⊗-context-++ Γ (⊗₀ Δ ∷ [])

  bundle : (Γ Δ : List Ob)
    → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
        ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id
      ≡ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .to
  bundle Γ Δ =
      ap₂ (λ (u : Hom (⊗-context (Γ ++ ⊗₀ Δ ∷ [])) (⊗-context Γ ⊗ (⊗₀ Δ ⊗ Unit)))
             (v : Hom (⊗-context (Γ ++ Δ ++ [])) (⊗-context (Γ ++ ⊗₀ Δ ∷ [])))
           → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ))) ∘ u) ∘ v)
          (plug-id [] Γ (⊗₀ Δ ∷ [])) (plug-id Γ Δ [])
    ∙ bundle-core Γ Δ

  -- restrict₂.to of the unit-adjusted φ is the identity (⊗-arr = id).
  compute : (Γ Δ : List Ob)
    → Equiv.to (restrict₂-equiv {Γ} {Δ}) (φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ))) ≡ id
  compute Γ Δ =
      Hom-transport C (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) refl bundled
    ∙ ap (λ t → t ∘ (bundled ∘ reindex-from)) (ap (λ i → i .to) path→iso-refl)
    ∙ idl _
    ∙ ap (_∘ reindex-from) (bundle Γ Δ)
    ∙ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .invl
    where
      bundled = ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
             ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id
      reindex-from = path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .from

  -- The μ ↔ φ bridge: the strictification's comparison map μ is φ with the unit
  -- (re-)inserted on the second factor.
  μ-φ : (Γ Δ : List Ob)
      → μ Γ Δ ≡ φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ))
  μ-φ Γ Δ = Equiv.injective (restrict₂-equiv {Γ} {Δ})
              {x = μ Γ Δ} {y = φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ))}
              (restrict₂-μ Γ Δ ∙ sym (compute Γ Δ))

  -- General "tail" plug (empty prefix & suffix, arbitrary Γ-arg): plug the
  -- multimap m into the single slot, giving ρ→ ∘ m up to the ++[] reindex.
  plug-tail : (Γᵃ : List Ob) {x : Ob} (m : Hom (⊗-context Γᵃ) x)
    → plug [] Γᵃ [] m ≡ (ρ→ x ∘ m) ∘ (⊗-context-++-idr Γᵃ) .to
  plug-tail Γᵃ {x} m =
      plug-nil Γᵃ [] m
    ∙ ap ((m ◀ Unit) ∘_) (++[]-to-ρ→ Γᵃ)
    ∙ pulll (sym (MR.ρ→nat m))

  -- The ++[] reindex on a 2-element context is the identity (++-idr = refl there).
  idr-2elt : (a b : Ob) → (⊗-context-++-idr (a ∷ b ∷ [])) .to ≡ id
  idr-2elt a b =
    ap (λ i → i .to) (sym (⊗-context-++-idr-path (a ∷ b ∷ [])) ∙ path→iso-refl)

  -- A singleton-prefix, singleton-arg plug = ⊗ᵃ ▶ (ρ→ ∘ g) (plug-cons + plug-sing).
  plug-cons-sing : (a D E : Ob) (g : Hom (D ⊗ Unit) E)
    → plug (a ∷ []) (D ∷ []) [] g ≡ a ▶ (ρ→ E ∘ g)
  plug-cons-sing a D E g =
    plug-cons a [] (D ∷ []) [] g ∙ ap (a ▶_) (plug-sing D E g)

  -- φ expressed via μ (inverse of μ-φ): φ Γ Δ = μ Γ Δ ∘ (⊗Γ ▶ ρ→⊗Δ).
  φ≡μ : (Γ Δ : List Ob) → φ Γ Δ ≡ μ Γ Δ ∘ (⊗-context Γ ▶ ρ→ (⊗-context Δ))
  φ≡μ Γ Δ = sym
    ( ap (_∘ (⊗-context Γ ▶ ρ→ (⊗-context Δ))) (μ-φ Γ Δ)
    ∙ cancelr (▶.annihilate (ρ≅ .invr)) )

  -- ==========================================================================
  -- The strong monoidal structure on `Comparison`.
  -- ==========================================================================

  private module Cmp = Functor Comparison

  -- The action of Comparison on morphisms, with explicit source/target lists
  -- (definitionally `Cmp.F₁`, but avoids ⊗₀-non-injectivity inference blocks).
  Fₘ : (Γ Δ : List Ob)
     → Hom (⊗-context Γ ⊗ Unit) (⊗-context Δ) → Hom (⊗-context Γ) (⊗-context Δ)
  Fₘ Γ Δ f = f ∘ ρ→ (⊗-context Γ)

  -- The "reversed triangle": α← ∘ (a ▶ λ→) = ρ→ ◀.  This is 1lab's
  -- `triangle-inv` (Cat.Bi.Reasoning), instantiated at the delooping of M₀.
  tri← : (a x : Ob) → α← (a , Unit , x) ∘ (a ▶ λ→ x) ≡ ρ→ a ◀ x
  tri← a x = triangle-inv {f = a} {g = x}

  -- Collapsing the multicat composite (f⊗ₛg) ∘ₘ μ into plain C-composition,
  -- WITHOUT unfolding `plug` through the opaque μ: `plug-tail` + `idr-2elt` are
  -- applied as banked lemmas, so μ stays abstract (no normalization blow-up).
  lhs-collapse : {Γ Γ' Δ Δ' : List Ob}
    (f : Hom (⊗-context Γ ⊗ Unit) (⊗-context Γ'))
    (g : Hom (⊗-context Δ ⊗ Unit) (⊗-context Δ'))
    → _∘ₘ_ {Θ = []} {Ξ = []} {Γ = ⊗₀ Γ ∷ ⊗₀ Δ ∷ []} {x = ⊗₀ (Γ ++ Δ)}
        (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g) (μ Γ Δ)
      ≡ Cmp.F₁ {Γ ++ Δ} {Γ' ++ Δ'} (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g) ∘ μ Γ Δ
  lhs-collapse {Γ} {Γ'} {Δ} {Δ'} f g =
      ap (fg ∘_) (plug-tail (⊗₀ Γ ∷ ⊗₀ Δ ∷ []) (μ Γ Δ))
    ∙ ap (λ z → fg ∘ ((ρ→ (⊗₀ (Γ ++ Δ)) ∘ μ Γ Δ) ∘ z)) (idr-2elt (⊗₀ Γ) (⊗₀ Δ))
    ∙ ap (fg ∘_) (idr _)
    ∙ assoc fg (ρ→ (⊗₀ (Γ ++ Δ))) (μ Γ Δ)
    where fg = _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g

  -- The general F-mult naturality: φ conjugates the C-tensor of the images to
  -- the image of the Str-tensor.  Derived by translating the abstract Str-level
  -- `⊗ₛ-μ` through the μ ↔ φ bridge, keeping μ opaque throughout.
  nat-gen : {Γ Γ' Δ Δ' : List Ob}
    (f : Hom (⊗-context Γ ⊗ Unit) (⊗-context Γ'))
    (g : Hom (⊗-context Δ ⊗ Unit) (⊗-context Δ'))
    → φ Γ' Δ' ∘ (Fₘ Γ Γ' f ⊗₁ Fₘ Δ Δ' g)
      ≡ Fₘ (Γ ++ Δ) (Γ' ++ Δ') (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g) ∘ φ Γ Δ
  nat-gen {Γ} {Γ'} {Δ} {Δ'} f g = sym main
    where
      A  = ⊗-context Γ
      A' = ⊗-context Γ'
      B  = ⊗-context Δ
      B' = ⊗-context Δ'
      Ff = Fₘ Γ Γ' f
      Fg = Fₘ Δ Δ' g
      fg = _⊗ₛ_ {Γ} {Γ'} {Δ} {Δ'} f g

      -- The C-form of ⊗ₛ-μ's right-hand side (unfolding the two plugs).
      rhs-plug :
          _∘ₘ_ {Θ = ⊗₀ Γ ∷ []} {Ξ = []} {Γ = ⊗₀ Δ ∷ []} {x = ⊗₀ Δ'}
            (_∘ₘ_ {Θ = []} {Ξ = ⊗₀ Δ' ∷ []} {Γ = ⊗₀ Γ ∷ []} {x = ⊗₀ Γ'} (μ Γ' Δ') f) g
        ≡ (μ Γ' Δ' ∘ ((f ◀ (B' ⊗ Unit))
             ∘ (α← (A , Unit , B' ⊗ Unit) ∘ (A ▶ λ→ (B' ⊗ Unit)))))
            ∘ (A ▶ (ρ→ B' ∘ g))
      rhs-plug =
          ap (λ z → (μ Γ' Δ' ∘ plug [] (⊗₀ Γ ∷ []) (⊗₀ Δ' ∷ []) f) ∘ z)
             (plug-cons-sing (⊗₀ Γ) (⊗₀ Δ) (⊗₀ Δ') g)
        ∙ ap (λ z → (μ Γ' Δ' ∘ z) ∘ (A ▶ (ρ→ B' ∘ g)))
             (plug-nil (⊗₀ Γ ∷ []) (⊗₀ Δ' ∷ []) f)

      -- The bifunctor coherence at the heart of naturality: interchange
      -- (-⊗-.rlmap) slides Ff past the ρ-whiskers, which then annihilate.
      ρ-whisker-collapse-to-φ : (A' ▶ ρ← B') ∘ ((Ff ◀ (B' ⊗ Unit)) ∘ (A ▶ ρ→ B')) ≡ Ff ◀ B'
      ρ-whisker-collapse-to-φ =
        pulll (-⊗-.rlmap _ _) ∙ cancelr (▶.annihilate (ρ≅ .invr))

      -- The coherence: the unfolded RHS of ⊗ₛ-μ, post-composed with (A ▶ ρ→ B),
      -- collapses to φ Γ' Δ' ∘ (Ff ⊗₁ Fg).
      collapse-to-φ :
          ((μ Γ' Δ' ∘ ((f ◀ (B' ⊗ Unit))
             ∘ (α← (A , Unit , B' ⊗ Unit) ∘ (A ▶ λ→ (B' ⊗ Unit)))))
            ∘ (A ▶ (ρ→ B' ∘ g))) ∘ (A ▶ ρ→ B)
        ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
      collapse-to-φ =
          ap (λ z → ((μ Γ' Δ' ∘ ((f ◀ (B' ⊗ Unit)) ∘ z)) ∘ (A ▶ (ρ→ B' ∘ g))) ∘ (A ▶ ρ→ B))
             (tri← A (B' ⊗ Unit))
        ∙ ap (λ z → ((μ Γ' Δ' ∘ z) ∘ (A ▶ (ρ→ B' ∘ g))) ∘ (A ▶ ρ→ B))
             (sym (◀.F-∘ f (ρ→ A)))
        ∙ merge-g
        where
          -- (A ▶ (ρ→ B' ∘ g)) ∘ (A ▶ ρ→ B) = (A ▶ ρ→ B') ∘ (A ▶ Fg)
          g-split : (A ▶ (ρ→ B' ∘ g)) ∘ (A ▶ ρ→ B) ≡ (A ▶ ρ→ B') ∘ (A ▶ Fg)
          g-split = ▶.weave (sym (assoc (ρ→ B') g (ρ→ B)))
          reshape :
              ((φ Γ' Δ' ∘ (A' ▶ ρ← B')) ∘ (Ff ◀ (B' ⊗ Unit))) ∘ ((A ▶ ρ→ B') ∘ (A ▶ Fg))
            ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
          reshape = pullr (assoc _ _ _) ∙ pullr (pulll ρ-whisker-collapse-to-φ)
          merge-g :
              ((μ Γ' Δ' ∘ (Ff ◀ (B' ⊗ Unit))) ∘ (A ▶ (ρ→ B' ∘ g))) ∘ (A ▶ ρ→ B)
            ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
          merge-g =
              pullr g-split
            ∙ ap (λ z → (z ∘ (Ff ◀ (B' ⊗ Unit))) ∘ ((A ▶ ρ→ B') ∘ (A ▶ Fg))) (μ-φ Γ' Δ')
            ∙ reshape

      main :
          Fₘ (Γ ++ Δ) (Γ' ++ Δ') fg ∘ φ Γ Δ ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
      main =
          ap (Fₘ (Γ ++ Δ) (Γ' ++ Δ') fg ∘_) (φ≡μ Γ Δ)
        ∙ assoc (Fₘ (Γ ++ Δ) (Γ' ++ Δ') fg) (μ Γ Δ) (A ▶ ρ→ B)
        ∙ ap (_∘ (A ▶ ρ→ B)) (sym (lhs-collapse {Γ} {Γ'} {Δ} {Δ'} f g))
        ∙ ap (_∘ (A ▶ ρ→ B)) (⊗ₛ-μ {Γ} {Γ'} {Δ} {Δ'} f g)
        ∙ ap (_∘ (A ▶ ρ→ B)) rhs-plug
        ∙ collapse-to-φ

  -- Left-whisker naturality of φ (the `is-natural-◀` square), by specialising
  -- `nat-gen` at g = idₘ (F₁ idₘ = id) and folding the ⊗₁ into a ◀.
  nat-◀ : {Γ Γ' Δ : List Ob} (f : Hom (⊗-context Γ ⊗ Unit) (⊗-context Γ'))
    → Cmp.F₁ {Γ ++ Δ} {Γ' ++ Δ} (_⊗ₛ_ {Γ} {Γ'} {Δ} {Δ} f idₘ) ∘ φ Γ Δ
      ≡ φ Γ' Δ ∘ (Fₘ Γ Γ' f ◀ ⊗-context Δ)
  nat-◀ {Γ} {Γ'} {Δ} f =
      sym (nat-gen {Γ} {Γ'} {Δ} {Δ} f idₘ)
    ∙ ap (φ Γ' Δ ∘_)
         ( ap (Fₘ Γ Γ' f ⊗₁_) (Cmp.F-id {Δ})
         ∙ sym (-⊗-.lmap-◆ (Fₘ Γ Γ' f)) )

  -- Right-whisker naturality of φ (the `is-natural-▶` square), by specialising
  -- `nat-gen` at f = idₘ and folding the ⊗₁ into a ▶.
  nat-▶ : {Γ Δ Δ' : List Ob} (g : Hom (⊗-context Δ ⊗ Unit) (⊗-context Δ'))
    → Cmp.F₁ {Γ ++ Δ} {Γ ++ Δ'} (_⊗ₛ_ {Γ} {Γ} {Δ} {Δ'} idₘ g) ∘ φ Γ Δ
      ≡ φ Γ Δ' ∘ (⊗-context Γ ▶ Fₘ Δ Δ' g)
  nat-▶ {Γ} {Δ} {Δ'} g =
      sym (nat-gen {Γ} {Γ} {Δ} {Δ'} idₘ g)
    ∙ ap (φ Γ Δ' ∘_)
         ( ap (_⊗₁ Fₘ Δ Δ' g) (Cmp.F-id {Γ})
         ∙ sym (-⊗-.rmap-◆ (Fₘ Δ Δ' g)) )

  -- The tensor-comparison natural isomorphism, assembled from the componentwise
  -- iso φ and the two whisker-naturality squares.  Gives both `F-mult` and its
  -- invertibility.
  F-mult-iso :
    precompose₂ -⊗- Comparison Comparison ≅ⁿ postcompose₂ Comparison (Monoidal-category.-⊗- Str-monoidal)
  F-mult-iso = biiso→isoⁿ
    (λ Γ Δ → ⊗-context-++ Γ Δ Iso⁻¹)
    (λ {x} {y} {z} f → nat-◀ {x} {y} {z} f)
    (λ {x} {y} {z} f → nat-▶ {z} {x} {y} f)

  -- Object-level action of the comparison functor, and the bridge relating the
  -- image of a Str `path→iso` (living in Unary M) to C's own `path→iso`.
  Cmp-hom : {X Y : Ob} → Hom (X ⊗ Unit) Y → Hom X Y
  Cmp-hom {X} m = m ∘ ρ→ X

  bridge : {X Y : Ob} (r : X ≡ Y) → Cmp-hom (≅to r) ≡ path→iso {C = C} r .to
  bridge {X} = J (λ Y r → Cmp-hom (≅to r) ≡ path→iso {C = C} r .to)
    (ap Cmp-hom ≅to-refl ∙ ρ≅ {X} .invr ∙ sym (ap (λ i → i .to) path→iso-refl))

  -- The image of Str's strict associator is C's ⊗-context associativity iso.
  F₁-α→ : (A B C' : List Ob)
    → Cmp.F₁ {(A ++ B) ++ C'} {A ++ (B ++ C')}
        (Monoidal-category.α→ Str-monoidal (A , B , C'))
      ≡ ++-assoc-⊗-iso A B C' .to
  F₁-α→ A B C' =
      bridge (ap ⊗-context (++-assoc A B C'))
    ∙ ap (λ i → i .to) (++-assoc-⊗-path A B C')

  -- The right-unitor reindex: (⊗-context-++-idr A).to ∘ φ A [] = ρ← (⊗A).
  -- From `++[]-to-ρ→`: idr.to = ρ← ∘ ++[].to, and the ++[] iso cancels.
  ρ←-reindex : (A : List Ob)
    → (⊗-context-++-idr A) .to ∘ (⊗-context-++ A []) .from ≡ ρ← (⊗-context A)
  ρ←-reindex A =
      ap (_∘ (⊗-context-++ A []) .from)
         (introl (ρ≅ .invr) ∙ pullr (sym (++[]-to-ρ→ A)))
    ∙ cancelr (⊗-context-++ A [] .invl)

  -- The image of Str's strict right unitor.
  F₁-ρ← : (A : List Ob)
    → Cmp.F₁ {A ++ []} {A}
        (Monoidal-category.ρ← Str-monoidal A)
      ≡ (⊗-context-++-idr A) .to
  F₁-ρ← A =
      ap (Cmp.F₁ {A ++ []} {A}) (≅from-to (ap ⊗-context (sym (++-idr A))))
    ∙ bridge (sym (ap ⊗-context (sym (++-idr A))))
    ∙ ap (λ i → i .to) (⊗-context-++-idr-path A)

  -- The three monoidal coherence laws.  Associativity reduces to Repr's hexagon
  -- `F-α→` after rewriting the image of Str's strict associator; the unit laws
  -- collapse via `Comparison`'s F-id / the ⊗-context-++ unit legs.
  F-α→-proof : (A B C' : List Ob)
    → Cmp.F₁ {(A ++ B) ++ C'} {A ++ (B ++ C')}
        (Monoidal-category.α→ Str-monoidal (A , B , C'))
      ∘ φ (A ++ B) C' ∘ (φ A B ◀ ⊗-context C')
    ≡ φ A (B ++ C') ∘ (⊗-context A ▶ φ B C')
        ∘ α→ (⊗-context A , ⊗-context B , ⊗-context C')
  F-α→-proof A B C' =
      ap (_∘ (φ (A ++ B) C' ∘ (φ A B ◀ ⊗-context C'))) (F₁-α→ A B C')
    ∙ F-α→ A B C'

  F-λ←-proof : (A : List Ob)
    → Cmp.F₁ {A} {A} (Monoidal-category.λ← Str-monoidal A)
      ∘ φ [] A ∘ (id ◀ ⊗-context A)
    ≡ λ← (⊗-context A)
  F-λ←-proof A =
      ap (_∘ (φ [] A ∘ (id ◀ ⊗-context A))) (Cmp.F-id {A})
    ∙ idl _
    ∙ ap (φ [] A ∘_) ◀.F-id
    ∙ idr _

  F-ρ←-proof : (A : List Ob)
    → Cmp.F₁ {A ++ []} {A} (Monoidal-category.ρ← Str-monoidal A)
      ∘ φ A [] ∘ (⊗-context A ▶ id)
    ≡ ρ← (⊗-context A)
  F-ρ←-proof A =
      ap (λ z → Cmp.F₁ {A ++ []} {A} (Monoidal-category.ρ← Str-monoidal A) ∘ (φ A [] ∘ z))
         ▶.F-id
    ∙ ap (Cmp.F₁ {A ++ []} {A} (Monoidal-category.ρ← Str-monoidal A) ∘_) (idr _)
    ∙ ap (_∘ φ A []) (F₁-ρ← A)
    ∙ ρ←-reindex A

  private module MF = MonF Str-monoidal M₀

  -- The strong monoidal structure on the comparison functor: `Comparison` is a
  -- monoidal equivalence C^str ≃ C, the full coherence-theorem statement.
  Comparison-monoidal : MF.Monoidal-functor-on Comparison
  Comparison-monoidal = record
    { lax = record
      { ε = id
      ; F-mult = Isoⁿ.to F-mult-iso
      ; F-α→ = λ {A} {B} {C'} → F-α→-proof A B C'
      ; F-λ← = λ {A} → F-λ←-proof A
      ; F-ρ← = λ {A} → F-ρ←-proof A
      }
    ; ε-inv = id-invertible
    ; F-mult-inv = isoⁿ→is-invertibleⁿ F-mult-iso
    }

  -- ==========================================================================
  -- The coherence theorem, in one statement: every monoidal category is
  -- monoidally equivalent to a strict monoidal category — there is a strict
  -- monoidal category (Str, Str-monoidal) and a strong monoidal functor
  -- Str → C whose underlying functor is an equivalence of categories.
  -- ==========================================================================
  monoidal-strictification
    : Σ[ Cˢ ∈ Precategory o h ]
      Σ[ Mˢ ∈ Monoidal-category Cˢ ]
      ( is-strict-monoidal Mˢ
      × Σ[ F ∈ Functor Cˢ C ]
        ( MonF.Monoidal-functor-on Mˢ M₀ F
        × is-equivalence F ) )
  monoidal-strictification =
      Str , Str-monoidal , Str-is-strict
    , Comparison , Comparison-monoidal , Comparison-is-equivalence
