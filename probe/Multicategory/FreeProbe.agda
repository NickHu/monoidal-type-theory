open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties
open import Data.Set.Coequaliser using (_/_ ; inc ; quot)

open import Multicategory

module Multicategory.FreeProbe where

-- Shulman's simple type theory for monoidal categories (catlog draft,
-- Figure 2.2) over a multigraph G, presented intrinsically: terms ARE
-- derivations (nameless, indexed by context and type), so linearity
-- (Lemma 2.4.7) and unique derivations (Lemma 2.4.8) hold by construction
-- and substitution is capture-free by design.  The Γ|Δ annotation Shulman
-- puts on match⊗ to make type-checking unique is exactly the constructor's
-- implicit context arguments here.
--
-- NOTE (typo in the source): Figure 2.2's 1E rule has premise Γ,Δ ⊢ N : A
-- with conclusion ⋯ : C; Figure 2.4 (p. 111) restates the same rule with
-- premise Γ,Δ ⊢ N : C, which is the intended reading and the one
-- formalised here.
--
-- Substitution (Figure 2.3) is the admissible single-variable cut of
-- Lemma 2.4.9.  Its type is exactly the _∘ₘ_ field of Premulticategory,
--   Tm (Θ ++ x ∷ Ξ) z → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) z,
-- with the slot witnessed by the structural datatype Split below (not by a
-- path), so the definition needs no decidability of type equality and no
-- set-level assumptions — matching the design invariants of Multicategory.
--
-- The β/η-congruence _≈_ closes the file; quotienting Tm by it yields the
-- hom-sets of the free representable multicategory FMonCat G (the syntactic
-- multicategory of Theorem 2.4.10).  The multicategory laws for `sub` and
-- the universality of ⦅var,var⦆/⋆ are future work; see the module comment
-- at the end for the roadmap.

private variable
  o h : Level

-- A multigraph (Shulman §2.2): generating objects, and generating
-- multi-arrows from a list of objects to an object.  No composition, no
-- identities, and — as everywhere in this development — no assumption that
-- Ob is a set.
record Multigraph (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    Ob  : Type o
    Hom : List Ob → Ob → Type h

module Syntax {o h} (G : Multigraph o h) where
  private module G = Multigraph G

  -- Types (⊢ A type): base types from G, tensor, unit.
  data Ty : Type o where
    base : G.Ob → Ty
    _⊗_  : Ty → Ty → Ty
    𝟙    : Ty

  infixr 25 _⊗_

  Ctx : Type o
  Ctx = List Ty

  ⟦_⟧ᵍ : List G.Ob → Ctx
  ⟦_⟧ᵍ = map base

  private variable
    x z A B C : Ty
    Γ Δ Θ Ξ Ψ Ρ : Ctx
    As : List G.Ob

  -- ==========================================================================
  -- Terms-as-derivations (Figure 2.2), mutually with spines: the n premises
  -- of the generator rule, contexts concatenated.  Every constructor
  -- targets a fully general index built from its arguments, which keeps
  -- indexed matching in the without-K-friendly fragment.
  -- ==========================================================================

  data Tm : Ctx → Ty → Type (o ⊔ h)
  data Sp : Ctx → List G.Ob → Type (o ⊔ h)

  data Tm where
    -- id:  x : A ⊢ x : A
    var : Tm (A ∷ []) A
    -- fI:  f ∈ G(A₁,…,Aₙ; B) and Γᵢ ⊢ Mᵢ : Aᵢ  ⟹  Γ₁,…,Γₙ ⊢ f(M₁,…,Mₙ) : B
    gen : ∀ {B} → G.Hom As B → Sp Γ As → Tm Γ (base B)
    -- ⊗I:  Γ ⊢ M : A and Δ ⊢ N : B  ⟹  Γ,Δ ⊢ ⦅M,N⦆ : A ⊗ B
    ⦅_,_⦆ : Tm Γ A → Tm Δ B → Tm (Γ ++ Δ) (A ⊗ B)
    -- ⊗E:  Ψ ⊢ M : A ⊗ B and Γ,x:A,y:B,Δ ⊢ N : C  ⟹  Γ,Ψ,Δ ⊢ match⊗(M,xy.N) : C
    match⊗ : Tm Ψ (A ⊗ B) → Tm (Γ ++ A ∷ B ∷ Δ) C → Tm (Γ ++ Ψ ++ Δ) C
    -- 1I:  () ⊢ ⋆ : 𝟙
    ⋆ : Tm [] 𝟙
    -- 1E:  Ψ ⊢ M : 𝟙 and Γ,Δ ⊢ N : C  ⟹  Γ,Ψ,Δ ⊢ match𝟙(M,N) : C
    match𝟙 : Tm Ψ 𝟙 → Tm (Γ ++ Δ) C → Tm (Γ ++ Ψ ++ Δ) C

  data Sp where
    []  : Sp [] []
    _∷_ : ∀ {A} → Tm Γ (base A) → Sp Δ As → Sp (Γ ++ Δ) (A ∷ As)

  -- The identity spine: each generating object consumed by its own variable.
  id-sp : ∀ As → Sp ⟦ As ⟧ᵍ As
  id-sp []       = []
  id-sp (A ∷ As) = _∷_ {Γ = base A ∷ []} var (id-sp As)

  -- A generator, as a term in its context of variables.
  generator : ∀ {B} → G.Hom As B → Tm ⟦ As ⟧ᵍ (base B)
  generator f = gen f (id-sp _)

  -- ==========================================================================
  -- Slots.  Split x Θ Ρ Ξ structurally witnesses Ρ = Θ ++ x ∷ Ξ; being
  -- cons-by-cons data rather than a path, substitution can recurse on it
  -- and folds will reduce through it, in the style of the reassociation
  -- discipline of Multicategory.agda.
  -- ==========================================================================

  data Split (x : Ty) : Ctx → Ctx → Ctx → Type o where
    here  : Split x [] (x ∷ Ξ) Ξ
    there : ∀ {a} → Split x Θ Ρ Ξ → Split x (a ∷ Θ) (a ∷ Ρ) Ξ

  -- The canonical split of Θ ++ x ∷ Ξ at its marked slot.
  split-here : ∀ Θ (x : Ty) (Ξ : Ctx) → Split x Θ (Θ ++ x ∷ Ξ) Ξ
  split-here []      x Ξ = here
  split-here (a ∷ Θ) x Ξ = there (split-here Θ x Ξ)

  -- The path a split witnesses (cons-by-cons structural, never ∙-composed).
  split-path : Split x Θ Ρ Ξ → Θ ++ x ∷ Ξ ≡ Ρ
  split-path here      = refl
  split-path (there s) = ap (_ ∷_) (split-path s)

  -- Weaken a split by a suffix, or by a prefix (both structural).
  split-++ˡ : ∀ {Γ₁} → Split x Θ Γ₁ Ξ → ∀ Γ₂ → Split x Θ (Γ₁ ++ Γ₂) (Ξ ++ Γ₂)
  split-++ˡ here      Γ₂ = here
  split-++ˡ (there s) Γ₂ = there (split-++ˡ s Γ₂)

  split-++ʳ : ∀ {Γ₂} (Γ₁ : Ctx) → Split x Θ Γ₂ Ξ → Split x (Γ₁ ++ Θ) (Γ₁ ++ Γ₂) Ξ
  split-++ʳ []       s = s
  split-++ʳ (a ∷ Γ₁) s = there (split-++ʳ Γ₁ s)

  -- Deciding which side of a concatenation a slot falls in.  The outcome
  -- carries a split of that side plus the (structurally built) relation
  -- between the outer and inner boundary contexts.  No decidability of Ty
  -- is used: the decision recurses on Γ₁ and the split itself.
  data Split-++ (x : Ty) (Γ₁ Γ₂ Θ Ξ : Ctx) : Type o where
    on-left  : ∀ {Ξ₁} → Split x Θ Γ₁ Ξ₁ → Ξ₁ ++ Γ₂ ≡ Ξ → Split-++ x Γ₁ Γ₂ Θ Ξ
    on-right : ∀ {Θ₂} → Split x Θ₂ Γ₂ Ξ → Γ₁ ++ Θ₂ ≡ Θ → Split-++ x Γ₁ Γ₂ Θ Ξ

  split-++ : ∀ (Γ₁ : Ctx) {Γ₂} → Split x Θ (Γ₁ ++ Γ₂) Ξ → Split-++ x Γ₁ Γ₂ Θ Ξ
  split-++ []       s         = on-right s refl
  split-++ (a ∷ Γ₁) here      = on-left here refl
  split-++ (a ∷ Γ₁) (there s) with split-++ Γ₁ s
  ... | on-left  s₁ p = on-left (there s₁) p
  ... | on-right s₂ q = on-right s₂ (ap (a ∷_) q)

  -- ==========================================================================
  -- Substitution (Figure 2.3): the admissible cut of Lemma 2.4.9, by
  -- recursion on the target derivation.  Result contexts are reconciled by
  -- the structural reassociations below (each cons-by-cons; the residual
  -- ap's along the p/q returned by split-++ are themselves structural).
  -- ==========================================================================

  cast : Ρ ≡ Γ → Tm Ρ z → Tm Γ z
  cast p = subst (λ Ρ → Tm Ρ _) p

  sp-cast : Ρ ≡ Γ → Sp Ρ As → Sp Γ As
  sp-cast p = subst (λ Ρ → Sp Ρ _) p

  -- The slot was in the left region of a concatenation: flatten the suffix.
  --   (Θ ++ Γ ++ Ξ₁) ++ Δ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ)
  flattenˡ : ∀ Θ Γ Ξ₁ Δ → (Θ ++ Γ ++ Ξ₁) ++ Δ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ)
  flattenˡ []      Γ Ξ₁ Δ = ++-assoc Γ Ξ₁ Δ
  flattenˡ (a ∷ Θ) Γ Ξ₁ Δ = ap (a ∷_) (flattenˡ Θ Γ Ξ₁ Δ)

  -- The slot was in the right region: bury the prefix.
  --   Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
  flattenʳ : ∀ Γ₁ Θ₂ Γ Ξ → Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
  flattenʳ []       Θ₂ Γ Ξ = refl
  flattenʳ (a ∷ Γ₁) Θ₂ Γ Ξ = ap (a ∷_) (flattenʳ Γ₁ Θ₂ Γ Ξ)

  -- The slot was in the middle region of a three-part context.
  --   Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ Δ ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δ)
  flattenᵐ : ∀ Γm Θ₂ Γ Ξ₁ Δ
           → Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δ) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δ)
  flattenᵐ []       Θ₂ Γ Ξ₁ Δ = flattenˡ Θ₂ Γ Ξ₁ Δ
  flattenᵐ (a ∷ Γm) Θ₂ Γ Ξ₁ Δ = ap (a ∷_) (flattenᵐ Γm Θ₂ Γ Ξ₁ Δ)

  -- The slot was in the last region: bury both prefixes.
  --   Γm ++ Ψ ++ (Θ₃ ++ Ρ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Ρ
  bury : ∀ Γm Ψ Θ₃ Ρ → Γm ++ Ψ ++ (Θ₃ ++ Ρ) ≡ (Γm ++ (Ψ ++ Θ₃)) ++ Ρ
  bury []       Ψ Θ₃ Ρ = sym (++-assoc Ψ Θ₃ Ρ)
  bury (a ∷ Γm) Ψ Θ₃ Ρ = ap (a ∷_) (bury Γm Ψ Θ₃ Ρ)

  -- No split points into the empty context ("?[M/x] cannot happen").
  split-[] : Split x Θ [] Ξ → ⊥
  split-[] ()

  -- x[M/x] = M, with the vacuous boundary Γ ++ [] restored.  (This is what
  -- will make the right identity law of the syntactic multicategory a
  -- transport-filler.)  A standalone helper so that sub itself always
  -- matches the term first — splitting on the Split first strands the
  -- coverage checker on Γ ++ Δ ≟ x ∷ Ξ for the other term constructors.
  sub-var : Split x Θ (z ∷ []) Ξ → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) z
  sub-var {Γ = Γ} here      g = cast (sym (++-idr Γ)) g
  sub-var (there s) g = absurd (split-[] s)

  sub    : Split x Θ Ρ Ξ → Tm Ρ z → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) z
  sub-sp : Split x Θ Ρ Ξ → Sp Ρ As → Tm Γ x → Sp (Θ ++ Γ ++ Ξ) As

  sub s var g = sub-var s g

  -- f(…)[M/x]: push into the unique spine component containing the slot.
  sub s (gen f sp) g = gen f (sub-sp s sp g)

  -- ⦅P,Q⦆[M/x]: by split-++, the slot is in P xor in Q.
  sub {Θ = Θ} {Ξ = Ξ} {Γ = Γ} s (⦅_,_⦆ {Γ = Γ₁} {Δ = Δ₁} P Q) g
    with split-++ Γ₁ s
  ... | on-left {Ξ₁} s₁ p =
        cast (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
          ⦅ sub s₁ P g , Q ⦆
  ... | on-right {Θ₂} s₂ q =
        cast (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
          ⦅ P , sub s₂ Q g ⦆

  -- match⊗(P, xy.Q)[M/x]: three regions — Q's left part, P itself, or Q's
  -- right part.  Substituting under the binder weakens the split across the
  -- two bound slots x,y (split-++ˡ / split-++ʳ); note (A ∷ B ∷ []) ++ Δm
  -- and friends all reduce definitionally.
  sub {Θ = Θ} {Ξ = Ξ} {Γ = Γ} s (match⊗ {Ψ = Ψ} {A} {B} {Γ = Γm} {Δ = Δm} P Q) g
    with split-++ Γm s
  ... | on-left {Ξ₁} s₁ p =
        cast (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
          (match⊗ P
            (cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
              (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g)))
  ... | on-right {Θ₂} s' q with split-++ Ψ s'
  ...   | on-left {Ξ₁} s₁ p =
          cast (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
            (match⊗ (sub s₁ P g) Q)
  ...   | on-right {Θ₃} s₂ q₂ =
          cast (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
            (match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P
              (cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
                (sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q g)))

  -- ⋆[M/x] cannot happen: no split points into the empty context.
  sub s ⋆ g = absurd (split-[] s)

  -- match𝟙(P, Q)[M/x]: as for match⊗, but with no bound slots.
  sub {Θ = Θ} {Ξ = Ξ} {Γ = Γ} s (match𝟙 {Ψ = Ψ} {Γ = Γm} {Δ = Δm} P Q) g
    with split-++ Γm s
  ... | on-left {Ξ₁} s₁ p =
        cast (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
          (match𝟙 P
            (cast (sym (flattenˡ Θ Γ Ξ₁ Δm))
              (sub (split-++ˡ s₁ Δm) Q g)))
  ... | on-right {Θ₂} s' q with split-++ Ψ s'
  ...   | on-left {Ξ₁} s₁ p =
          cast (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
            (match𝟙 (sub s₁ P g) Q)
  ...   | on-right {Θ₃} s₂ q₂ =
          cast (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
            (match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P
              (cast (sym (flattenʳ Γm Θ₃ Γ Ξ))
                (sub (split-++ʳ Γm s₂) Q g)))

  sub-sp s [] g = absurd (split-[] s)
  sub-sp {Θ = Θ} {Ξ = Ξ} {Γ = Γ} s (_∷_ {Γ = Γ₁} {Δ = Δ₁} t ts) g
    with split-++ Γ₁ s
  ... | on-left {Ξ₁} s₁ p =
        sp-cast (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
          (sub s₁ t g ∷ ts)
  ... | on-right {Θ₂} s₂ q =
        sp-cast (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
          (t ∷ sub-sp s₂ ts g)

