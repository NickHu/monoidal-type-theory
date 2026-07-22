open import 1Lab.Prelude hiding (id ; _∘_)
open import Cat.Base
open Cat.Base._=>_ using (is-natural)
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Cat.Univalent using (path→iso ; Hom-transport)
open import Cat.Functor.Naturality
import Cat.Monoidal.Reasoning as MonR
open import Cat.Functor.Properties
open import Cat.Functor.Equivalence
open import Cat.Functor.Bifunctor using (Bifunctor ; biiso→isoⁿ)
open import Cat.Functor.Compose using (precompose₂ ; postcompose₂)
import Cat.Monoidal.Functor as MonF
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory
open import Multicategory.Unary
open import Multicategory.Instances.Monoidal
import Multicategory.Representable as Rep
import Multicategory.Strictification as Strict

-- The strictification of the representable multicategory of a monoidal category
-- C is equivalent, as a plain category, to C itself.  This is the underlying
-- (category-level) content of the coherence theorem: the strict monoidal
-- category `C^str = Str` and the original C have equivalent underlying
-- categories.
--
-- The comparison functor `Str → C` sends a context Γ to its tensor ⊗-context Γ
-- and a strict morphism f : (⊗Γ ⊗ Unit) → ⊗Δ to `f ∘ ρ→` : ⊗Γ → ⊗Δ.  The key
-- computation is that the multicategory composition, at singleton contexts,
-- reduces to plain composition conjugated by the right unitor:
--   plug [] (a ∷ []) [] m = ρ→ b ∘ m ,
-- so the functor's compositionality is pure associativity, and it is fully
-- faithful (precomposition with the unitor iso ρ→) and essentially surjective
-- (every object c is ⊗-context (c ∷ []) = c ⊗ Unit ≅ c).
module Multicategory.Instances.Monoidal.Coherence
  {o h} (C : Precategory o h) (M₀ : Monoidal-category C) where

  open Cr C
  open Monoidal-category M₀
  open Repr C M₀ using
    (⊗-context ; plug ; plug-nil ; plug-cons ; plug-id ; ⊗-context-++ ; ⊗-context-++-idr
    ; ⊗-context-++-idr-path ; ⊗-context-++-[]-ρ ; path→iso-ap-⊗ ; path→iso-refl ; φ
    ; ++-assoc-⊗-iso ; ++-assoc-⊗-path ; F-α→)

  private
    Mᵣ : Premulticategory o h
    Mᵣ = monoidal→multicategory C M₀

    rep : Rep.is-representable Mᵣ
    rep = monoidal→multicategory-is-representable C M₀

  open Premulticategory Mᵣ using (_∘ₘ_ ; idₘ)
  open Strict Mᵣ rep using
    (Str ; ⊗₀ ; ⊗-arr ; μ ; _⊗ₛ_ ; ⊗ₛ-μ ; restrict₂-equiv ; restrict₂-μ ; Str-monoidal
    ; ≅to ; ≅to-refl ; ≅from-to)

  private module MR = MonR M₀


  -- Singleton plug = right-unitor conjugation.  Uses `plug-nil`, the identity
  -- `(⊗-context-++ (a∷[]) []).to = ρ→ (a ⊗ Unit)` (from ⊗-context-++-[]-ρ, whose
  -- ++-idr factor is `▶ id = id`), and naturality of ρ→.
  plug-sing : (a b : Ob) (m : Hom (a ⊗ Unit) b)
    → plug [] (a ∷ []) [] m ≡ ρ→ b ∘ m
  plug-sing a b m =
      plug-nil (a ∷ []) [] m
    ∙ ap ((m ◀ Unit) ∘_) to≡ρ→
    ∙ sym (unitor-r.to .is-natural (a ⊗ Unit) b m)
    where
      to≡ρ→ : (⊗-context-++ (a ∷ []) []) .to ≡ ρ→ (a ⊗ Unit)
      to≡ρ→ =
          sym (idr _)
        ∙ ap ((⊗-context-++ (a ∷ []) []) .to ∘_) (sym ▶.F-id)
        ∙ ⊗-context-++-[]-ρ (a ∷ [])

  -- The comparison functor Str → C.
  Comparison : Functor Str C
  Comparison .Functor.F₀ Γ     = ⊗-context Γ
  Comparison .Functor.F₁ {Γ} f = f ∘ ρ→ (⊗-context Γ)
  -- F₁ id_Str = ρ← (⊗Γ) ∘ ρ→ (⊗Γ) = id  (id_Str = idₘ = ρ←).
  Comparison .Functor.F-id     = ρ≅ .invr
  -- F₁ (g ∘ₛ f) = (g ∘ ρ→⊗Δ ∘ f) ∘ ρ→⊗Γ = (g ∘ ρ→⊗Δ) ∘ (f ∘ ρ→⊗Γ) = F₁ g ∘ F₁ f.
  Comparison .Functor.F-∘ {Γ} {Δ} {Ε} g f =
      ap (_∘ ρ→ (⊗-context Γ)) (ap (g ∘_) (plug-sing (⊗-context Γ) (⊗-context Δ) f))
    ∙ sym (assoc g (ρ→ (⊗-context Δ) ∘ f) (ρ→ (⊗-context Γ)))
    ∙ ap (g ∘_) (sym (assoc (ρ→ (⊗-context Δ)) f (ρ→ (⊗-context Γ))))
    ∙ assoc g (ρ→ (⊗-context Δ)) (f ∘ ρ→ (⊗-context Γ))

  -- Fully faithful: the hom-action is precomposition with the iso ρ→ (⊗Γ).
  Comparison-ff : is-fully-faithful Comparison
  Comparison-ff {Γ} {Δ} = invertible-precomp-equiv (iso→invertible (ρ≅ {⊗-context Γ}))

  -- Split essentially surjective: c is hit by the singleton context (c ∷ []),
  -- since ⊗-context (c ∷ []) = c ⊗ Unit ≅ c (inverse right unitor).
  Comparison-eso : is-split-eso Comparison
  Comparison-eso c = (c ∷ []) , (ρ≅ {c} Iso⁻¹)

  -- Hence Str and C have equivalent underlying categories: C ≃ C^str.
  Comparison-is-equivalence : is-equivalence Comparison
  Comparison-is-equivalence =
    ff+split-eso→is-equivalence (λ {x} {y} → Comparison-ff {x} {y}) Comparison-eso

  -- ==========================================================================
  -- Monoidal structure ingredients (toward `Monoidal-functor-on Comparison`).
  -- ==========================================================================

  -- The comparison map φ Γ Δ = (⊗-context-++ Γ Δ).from : ⊗Γ ⊗ ⊗Δ → ⊗(Γ++Δ) is
  -- invertible (it is one leg of the ⊗-context-++ iso).  This is the F-mult-inv
  -- ingredient of the strong monoidal structure.
  φ-inv : (Γ Δ : List Ob) → is-invertible (φ Γ Δ)
  φ-inv Γ Δ = iso→invertible (⊗-context-++ Γ Δ Iso⁻¹)

  -- Bundling coherence (the heart of the μ ↔ φ bridge).  `restrict₂.to` of the
  -- unit-adjusted φ reduces, via `⊗-arr = id`, to two `plug _ _ _ id` legs; this
  -- lemma shows the whole composite is the list-reindexing iso, by induction on Γ.
  -- Associator naturality in the third slot (whiskering h): α→ slides a
  -- whiskered map from (a⊗b)▶h to a▶(b▶h).
  α-mid : (a b : Ob) {X Y : Ob} (h : Hom X Y)
    → α→ (a , b , Y) ∘ ((a ⊗ b) ▶ h) ≡ (a ▶ (b ▶ h)) ∘ α→ (a , b , X)
  α-mid a b {X} {Y} h = MR.▶-assoc {f = a} {g = b} .Isoⁿ.to .is-natural X Y h

  bundle : (Γ Δ : List Ob)
    → ((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← (⊗-context Δ)))
        ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id
      ≡ path→iso (ap ⊗-context (ap (Γ ++_) (++-idr Δ))) .to
  bundle [] Δ =
      ((φ [] Δ ∘ (⊗-context [] ▶ ρ← D)) ∘ ⌜ plug [] [] (D ∷ []) id ⌝) ∘ plug [] Δ [] id
    ≡⟨ ap! plugA ⟩
      ((λ← D ∘ (Unit ▶ ρ← D)) ∘ λ→ (D ⊗ Unit)) ∘ ⌜ plug [] Δ [] id ⌝
    ≡⟨ ap! plugB ⟩
      ((λ← D ∘ (Unit ▶ ρ← D)) ∘ λ→ (D ⊗ Unit)) ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ap (_∘ (⊗-context-++ Δ []) .to) (sym (assoc _ _ _)) ⟩
      (λ← D ∘ ((Unit ▶ ρ← D) ∘ λ→ (D ⊗ Unit))) ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ap (λ w → (λ← D ∘ w) ∘ (⊗-context-++ Δ []) .to)
          (sym (unitor-l.to .is-natural _ _ (ρ← D))) ⟩
      (λ← D ∘ (λ→ D ∘ ρ← D)) ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ap (_∘ (⊗-context-++ Δ []) .to) (assoc _ _ _) ⟩
      ((λ← D ∘ λ→ D) ∘ ρ← D) ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ap (λ w → (w ∘ ρ← D) ∘ (⊗-context-++ Δ []) .to) (λ≅ .invr) ⟩
      (id ∘ ρ← D) ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ap (_∘ (⊗-context-++ Δ []) .to) (idl _) ⟩
      ρ← D ∘ (⊗-context-++ Δ []) .to
    ≡⟨ ρ-reindex ⟩
      (⊗-context-++-idr Δ) .to
    ≡⟨ ap (λ i → i .to) (sym (⊗-context-++-idr-path Δ)) ⟩
      path→iso (ap ⊗-context (++-idr Δ)) .to
    ∎
    where
      D = ⊗-context Δ
      plugA : plug [] [] (D ∷ []) id ≡ λ→ (D ⊗ Unit)
      plugA = plug-nil [] (D ∷ []) id
            ∙ ap (_∘ (⊗-context-++ [] (D ∷ [])) .to) ◀.F-id ∙ idl _
      plugB : plug [] Δ [] id ≡ (⊗-context-++ Δ []) .to
      plugB = plug-nil Δ [] id
            ∙ ap (_∘ (⊗-context-++ Δ []) .to) ◀.F-id ∙ idl _
      ρ-reindex : ρ← D ∘ (⊗-context-++ Δ []) .to ≡ (⊗-context-++-idr Δ) .to
      ρ-reindex =
          sym (idr _)
        ∙ ap ((ρ← D ∘ (⊗-context-++ Δ []) .to) ∘_) (sym (⊗-context-++-idr Δ .invr))
        ∙ assoc _ _ _
        ∙ ap (_∘ (⊗-context-++-idr Δ) .to)
             ( sym (assoc _ _ _)
             ∙ ap (ρ← D ∘_) (⊗-context-++-[]-ρ Δ)
             ∙ ρ≅ .invr )
        ∙ idl _
  bundle (a ∷ Γ) Δ =
      step-▶ ∙ ap (a ▶_) (bundle Γ Δ)
    ∙ ap (λ i → i .to)
         (sym (path→iso-ap-⊗ a (ap ⊗-context (ap (Γ ++_) (++-idr Δ)))))
    where
      D = ⊗-context Δ
      plug-cons-id : plug [] (a ∷ Γ) (⊗₀ Δ ∷ []) id
          ≡ α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)
      plug-cons-id = plug-id [] (a ∷ Γ) (⊗₀ Δ ∷ [])
          ∙ ap (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘_)
               (ap (a ▶_) (sym (plug-id [] Γ (⊗₀ Δ ∷ []))))
      step-▶ :
          ((φ (a ∷ Γ) Δ ∘ (⊗-context (a ∷ Γ) ▶ ρ← D)) ∘ plug [] (a ∷ Γ) (⊗₀ Δ ∷ []) id)
            ∘ plug (a ∷ Γ) Δ [] id
        ≡ a ▶ (((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← D)) ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id)
      step-▶ =
          ((⌜ φ (a ∷ Γ) Δ ⌝ ∘ (⊗-context (a ∷ Γ) ▶ ρ← D)) ∘ plug [] (a ∷ Γ) (⊗₀ Δ ∷ []) id)
            ∘ plug (a ∷ Γ) Δ [] id
        ≡⟨ refl ⟩
          ((((a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , D)) ∘ (⊗-context (a ∷ Γ) ▶ ρ← D))
            ∘ ⌜ plug [] (a ∷ Γ) (⊗₀ Δ ∷ []) id ⌝) ∘ plug (a ∷ Γ) Δ [] id
        ≡⟨ ap! plug-cons-id ⟩
          ((((a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , D)) ∘ ((a ⊗ ⊗-context Γ) ▶ ρ← D))
            ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ ⌜ plug (a ∷ Γ) Δ [] id ⌝
        ≡⟨ ap! (plug-cons a Γ Δ [] id) ⟩
          ((((a ▶ φ Γ Δ) ∘ α→ (a , ⊗-context Γ , D)) ∘ ((a ⊗ ⊗-context Γ) ▶ ρ← D))
            ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → (z ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
                     ∘ (a ▶ plug Γ Δ [] id))
              (sym (assoc _ _ _)) ⟩
          (((a ▶ φ Γ Δ) ∘ (α→ (a , ⊗-context Γ , D) ∘ ((a ⊗ ⊗-context Γ) ▶ ρ← D)))
            ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → (((a ▶ φ Γ Δ) ∘ z)
                       ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
                     ∘ (a ▶ plug Γ Δ [] id))
              (α-mid a (⊗-context Γ) (ρ← D)) ⟩
          (((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ α→ (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit)))
            ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (_∘ (a ▶ plug Γ Δ [] id)) (sym (assoc _ _ _)) ⟩
          ((a ▶ φ Γ Δ) ∘ (((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ α→ (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit))
            ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id))))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → ((a ▶ φ Γ Δ) ∘ z) ∘ (a ▶ plug Γ Δ [] id)) (sym (assoc _ _ _)) ⟩
          ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D))
            ∘ (α→ (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit)
               ∘ (α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ z)) ∘ (a ▶ plug Γ Δ [] id))
              (assoc _ _ _) ⟩
          ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D))
            ∘ ((α→ (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit) ∘ α← (a , ⊗-context Γ , ⊗₀ Δ ⊗ Unit))
               ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id))))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ (z ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id))))
                     ∘ (a ▶ plug Γ Δ [] id))
              (α≅ .invl) ⟩
          ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ (id ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id))))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ z)) ∘ (a ▶ plug Γ Δ [] id))
              (idl _) ⟩
          ((a ▶ φ Γ Δ) ∘ ((a ▶ (⊗-context Γ ▶ ρ← D)) ∘ (a ▶ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (λ z → ((a ▶ φ Γ Δ) ∘ z) ∘ (a ▶ plug Γ Δ [] id)) (sym (▶.F-∘ _ _)) ⟩
          ((a ▶ φ Γ Δ) ∘ (a ▶ ((⊗-context Γ ▶ ρ← D) ∘ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ ap (_∘ (a ▶ plug Γ Δ [] id)) (sym (▶.F-∘ _ _)) ⟩
          (a ▶ (φ Γ Δ ∘ ((⊗-context Γ ▶ ρ← D) ∘ plug [] Γ (⊗₀ Δ ∷ []) id)))
            ∘ (a ▶ plug Γ Δ [] id)
        ≡⟨ sym (▶.F-∘ _ _) ⟩
          a ▶ ((φ Γ Δ ∘ ((⊗-context Γ ▶ ρ← D) ∘ plug [] Γ (⊗₀ Δ ∷ []) id)) ∘ plug Γ Δ [] id)
        ≡⟨ ap (λ z → a ▶ (z ∘ plug Γ Δ [] id)) (assoc _ _ _) ⟩
          a ▶ (((φ Γ Δ ∘ (⊗-context Γ ▶ ρ← D)) ∘ plug [] Γ (⊗₀ Δ ∷ []) id) ∘ plug Γ Δ [] id)
        ∎

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
    ∙ ap ((m ◀ Unit) ∘_) to≡
    ∙ assoc _ _ _
    ∙ ap (_∘ (⊗-context-++-idr Γᵃ) .to) (sym (unitor-r.to .is-natural _ _ m))
    where
      to≡ : (⊗-context-++ Γᵃ []) .to
          ≡ ρ→ (⊗-context Γᵃ) ∘ (⊗-context-++-idr Γᵃ) .to
      to≡ =
          sym (idr _)
        ∙ ap ((⊗-context-++ Γᵃ []) .to ∘_) (sym (⊗-context-++-idr Γᵃ .invr))
        ∙ assoc _ _ _
        ∙ ap (_∘ (⊗-context-++-idr Γᵃ) .to) (⊗-context-++-[]-ρ Γᵃ)

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
  φ≡μ Γ Δ =
      sym (idr (φ Γ Δ))
    ∙ ap (φ Γ Δ ∘_)
         ( sym ▶.F-id
         ∙ ap (⊗-context Γ ▶_) (sym (ρ≅ {⊗-context Δ} .invr))
         ∙ ▶.F-∘ _ _ )
    ∙ assoc (φ Γ Δ) (⊗-context Γ ▶ ρ← (⊗-context Δ)) (⊗-context Γ ▶ ρ→ (⊗-context Δ))
    ∙ ap (_∘ (⊗-context Γ ▶ ρ→ (⊗-context Δ))) (sym (μ-φ Γ Δ))

  -- ==========================================================================
  -- The strong monoidal structure on `Comparison`.
  -- ==========================================================================

  private module Cmp = Functor Comparison

  -- The action of Comparison on morphisms, with explicit source/target lists
  -- (definitionally `Cmp.F₁`, but avoids ⊗₀-non-injectivity inference blocks).
  Fₘ : (Γ Δ : List Ob)
     → Hom (⊗-context Γ ⊗ Unit) (⊗-context Δ) → Hom (⊗-context Γ) (⊗-context Δ)
  Fₘ Γ Δ f = f ∘ ρ→ (⊗-context Γ)

  -- The "reversed triangle": α← ∘ (a ▶ λ→) = ρ→ ◀ (the inverse of triangle-α→).
  tri← : (a x : Ob) → α← (a , Unit , x) ∘ (a ▶ λ→ x) ≡ ρ→ a ◀ x
  tri← a x =
      sym (idl _)
    ∙ ap (_∘ (α← (a , Unit , x) ∘ (a ▶ λ→ x))) (sym pinv)
    ∙ sym (assoc _ _ _)
    ∙ ap ((ρ→ a ◀ x) ∘_) PQ
    ∙ idr _
    where
      pinv : (ρ→ a ◀ x) ∘ (ρ← a ◀ x) ≡ id
      pinv = sym (◀.F-∘ _ _) ∙ ap (_◀ x) (ρ≅ {a} .invl) ∙ ◀.F-id
      PQ : (ρ← a ◀ x) ∘ (α← (a , Unit , x) ∘ (a ▶ λ→ x)) ≡ id
      PQ =
          ap (_∘ (α← (a , Unit , x) ∘ (a ▶ λ→ x))) (sym triangle-α→)
        ∙ sym (assoc _ _ _)
        ∙ ap ((a ▶ λ← x) ∘_) (assoc _ _ _)
        ∙ ap (λ w → (a ▶ λ← x) ∘ (w ∘ (a ▶ λ→ x))) (α≅ .invl)
        ∙ ap ((a ▶ λ← x) ∘_) (idl _)
        ∙ sym (▶.F-∘ _ _)
        ∙ ap (a ▶_) (λ≅ {x} .invr)
        ∙ ▶.F-id

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

      -- The bifunctor coherence at the heart of naturality.
      ρ-whisker-collapse-to-φ : (A' ▶ ρ← B') ∘ ((Ff ◀ (B' ⊗ Unit)) ∘ (A ▶ ρ→ B')) ≡ Ff ◀ B'
      ρ-whisker-collapse-to-φ =
          assoc _ _ _
        ∙ ap (_∘ (A ▶ ρ→ B')) step-a
        ∙ ap ((Ff ⊗₁ ρ← B') ∘_) (-⊗-.rmap-◆ (ρ→ B'))
        ∙ sym (-⊗-.◆-∘ {f = Ff} {g = id} {f' = ρ← B'} {g' = ρ→ B'})
        ∙ ap (λ z → z ⊗₁ (ρ← B' ∘ ρ→ B')) (idr Ff)
        ∙ ap (Ff ⊗₁_) (ρ≅ {B'} .invr)
        ∙ sym (-⊗-.lmap-◆ Ff)
        where
          step-a : (A' ▶ ρ← B') ∘ (Ff ◀ (B' ⊗ Unit)) ≡ Ff ⊗₁ ρ← B'
          step-a =
              ap (_∘ (Ff ◀ (B' ⊗ Unit))) (-⊗-.rmap-◆ (ρ← B'))
            ∙ ap ((id ⊗₁ ρ← B') ∘_) (-⊗-.lmap-◆ Ff)
            ∙ sym (-⊗-.◆-∘ {f = id} {g = Ff} {f' = ρ← B'} {g' = id})
            ∙ ap (λ z → z ⊗₁ (ρ← B' ∘ id)) (idl Ff)
            ∙ ap (Ff ⊗₁_) (idr (ρ← B'))

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
          g-split =
              sym (▶.F-∘ (ρ→ B' ∘ g) (ρ→ B))
            ∙ ap (A ▶_) (sym (assoc (ρ→ B') g (ρ→ B)))
            ∙ ▶.F-∘ (ρ→ B') Fg
          reshape :
              ((φ Γ' Δ' ∘ (A' ▶ ρ← B')) ∘ (Ff ◀ (B' ⊗ Unit))) ∘ ((A ▶ ρ→ B') ∘ (A ▶ Fg))
            ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
          reshape =
              ap (_∘ ((A ▶ ρ→ B') ∘ (A ▶ Fg))) (sym (assoc _ _ _))
            ∙ sym (assoc _ _ _)
            ∙ ap (φ Γ' Δ' ∘_)
                 ( assoc _ _ _
                 ∙ ap (_∘ (A ▶ Fg))
                      ( sym (assoc (A' ▶ ρ← B') (Ff ◀ (B' ⊗ Unit)) (A ▶ ρ→ B'))
                      ∙ ρ-whisker-collapse-to-φ ) )
          merge-g :
              ((μ Γ' Δ' ∘ (Ff ◀ (B' ⊗ Unit))) ∘ (A ▶ (ρ→ B' ∘ g))) ∘ (A ▶ ρ→ B)
            ≡ φ Γ' Δ' ∘ (Ff ⊗₁ Fg)
          merge-g =
              sym (assoc _ _ _)
            ∙ ap ((μ Γ' Δ' ∘ (Ff ◀ (B' ⊗ Unit))) ∘_) g-split
            ∙ ap (_∘ ((A ▶ ρ→ B') ∘ (A ▶ Fg))) (ap (_∘ (Ff ◀ (B' ⊗ Unit))) (μ-φ Γ' Δ'))
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
  ρ←-reindex : (A : List Ob)
    → (⊗-context-++-idr A) .to ∘ (⊗-context-++ A []) .from ≡ ρ← (⊗-context A)
  ρ←-reindex A =
      sym (idl _)
    ∙ ap (_∘ (h′ ∘ gi)) (sym (ρ≅ {⊗-context A} .invr))
    ∙ sym (assoc _ _ _)
    ∙ ap (ρ← (⊗-context A) ∘_) ρ→-cancel
    ∙ idr _
    where
      g  = (⊗-context-++ A []) .to
      gi = (⊗-context-++ A []) .from
      h′ = (⊗-context-++-idr A) .to
      hi = (⊗-context-++-idr A) .from
      ρ→-cancel : ρ→ (⊗-context A) ∘ (h′ ∘ gi) ≡ id
      ρ→-cancel =
          ap (_∘ (h′ ∘ gi)) (sym (⊗-context-++-[]-ρ A))
        ∙ sym (assoc _ _ _)
        ∙ ap (g ∘_)
             ( assoc _ _ _
             ∙ ap (_∘ gi) (⊗-context-++-idr A .invr)
             ∙ idl _ )
        ∙ ⊗-context-++ A [] .invl

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
