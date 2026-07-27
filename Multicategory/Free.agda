open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties
open import Data.Set.Coequaliser using (_/_ ; inc)

open import Multicategory
import ListPath.Solver

module Multicategory.Free where

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
-- multicategory of Theorem 2.4.10).  The multicategory laws for `sub`, the
-- universality of ⦅var,var⦆/⋆, and freeness are all proved in the Free/*
-- modules; see the module comment at the end for the map.

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

  -- The structural reassociation paths below are aliases of the generic
  -- list-path solver's, so ListPath.Solver's solve/list! vocabulary matches
  -- this module's boundaries definitionally.
  private module LP = ListPath.Solver.NbE Ty

  ⟦_⟧ᵍ : List G.Ob → Ctx
  ⟦_⟧ᵍ = map base

  private variable
    x z A B C : Ty
    Γ Δ Θ Ξ Ψ Ρ Γ₁ Δ₁ Ξ₁ Γm Δm Θ₂ Θ₃ : Ctx
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

  -- Deciding which side of a concatenation a slot falls in: a *view with
  -- soundness* on s.  Each branch carries the split of that side, the
  -- (structurally built) relation between the boundary contexts, AND a PathP
  -- reconstituting s from the weakened side-split over that relation — which
  -- is exactly what every proof about sub's branches needs.  No decidability
  -- of Ty is used: the decision recurses on Γ₁ and the split itself, and the
  -- soundness field is refl-or-cons at every step.
  data Split-++ (Γ₁ Γ₂ : Ctx) {x : Ty} {Θ Ξ : Ctx}
                (s : Split x Θ (Γ₁ ++ Γ₂) Ξ) : Type o where
    on-left  : ∀ {Ξ₁} (s₁ : Split x Θ Γ₁ Ξ₁) (p : Ξ₁ ++ Γ₂ ≡ Ξ)
             → PathP (λ i → Split x Θ (Γ₁ ++ Γ₂) (p i)) (split-++ˡ s₁ Γ₂) s
             → Split-++ Γ₁ Γ₂ s
    on-right : ∀ {Θ₂} (s₂ : Split x Θ₂ Γ₂ Ξ) (q : Γ₁ ++ Θ₂ ≡ Θ)
             → PathP (λ i → Split x (q i) (Γ₁ ++ Γ₂) Ξ) (split-++ʳ Γ₁ s₂) s
             → Split-++ Γ₁ Γ₂ s

  -- The cons step of the decision, as a named function so that proofs about
  -- split-++ are plain ap's (no with-abstraction anywhere).
  split-++-step : ∀ {Γ₁ Γ₂} {a : Ty} {s : Split x Θ (Γ₁ ++ Γ₂) Ξ}
                → Split-++ Γ₁ Γ₂ s → Split-++ (a ∷ Γ₁) Γ₂ (there s)
  split-++-step (on-left  s₁ p co) = on-left (there s₁) p (λ i → there (co i))
  split-++-step (on-right s₂ q co) = on-right s₂ (ap (_ ∷_) q) (λ i → there (co i))

  split-++ : ∀ (Γ₁ : Ctx) {Γ₂} (s : Split x Θ (Γ₁ ++ Γ₂) Ξ) → Split-++ Γ₁ Γ₂ s
  split-++ []       s         = on-right s refl refl
  split-++ (a ∷ Γ₁) here      = on-left here refl refl
  split-++ (a ∷ Γ₁) (there s) = split-++-step (split-++ Γ₁ s)

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
  flattenˡ : ∀ (Θ Γ Ξ₁ Δ : Ctx) → (Θ ++ Γ ++ Ξ₁) ++ Δ ≡ Θ ++ Γ ++ (Ξ₁ ++ Δ)
  flattenˡ = LP.flattenˡ

  -- The slot was in the right region: bury the prefix.
  --   Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
  flattenʳ : ∀ (Γ₁ Θ₂ Γ Ξ : Ctx) → Γ₁ ++ (Θ₂ ++ Γ ++ Ξ) ≡ (Γ₁ ++ Θ₂) ++ Γ ++ Ξ
  flattenʳ = LP.flattenʳ

  -- The slot was in the middle region of a three-part context.
  --   Γm ++ (Θ₂ ++ Γ ++ Ξ₁) ++ Δ ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δ)
  flattenᵐ : ∀ (Γm Θ₂ Γ Ξ₁ Δ : Ctx)
           → Γm ++ ((Θ₂ ++ Γ ++ Ξ₁) ++ Δ) ≡ (Γm ++ Θ₂) ++ Γ ++ (Ξ₁ ++ Δ)
  flattenᵐ = LP.flattenᵐ

  -- The slot was in the last region: bury both prefixes.
  --   Γm ++ Ψ ++ (Θ₃ ++ Ρ) ≡ (Γm ++ Ψ ++ Θ₃) ++ Ρ
  bury : ∀ (Γm Ψ Θ₃ Ρ : Ctx) → Γm ++ Ψ ++ (Θ₃ ++ Ρ) ≡ (Γm ++ (Ψ ++ Θ₃)) ++ Ρ
  bury = LP.bury

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

  -- sub dispatches on the term constructor and hands the split's view to a
  -- named branch handler (never `with`): proofs about sub then proceed by
  -- matching the view and using split-++'s computation lemmas, with each
  -- handler clause reducing definitionally.
  sub    : Split x Θ Ρ Ξ → Tm Ρ z → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) z
  sub-sp : Split x Θ Ρ Ξ → Sp Ρ As → Tm Γ x → Sp (Θ ++ Γ ++ Ξ) As

  -- ⦅P,Q⦆[M/x]: the slot is in P xor in Q.
  sub-pair : {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} → Split-++ Γ₁ Δ₁ s
           → Tm Γ₁ A → Tm Δ₁ B → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) (A ⊗ B)

  -- match⊗(P, xy.Q)[M/x]: three regions — Q's left part, P itself, or Q's
  -- right part; the first view splits off Γm, the second splits Ψ ++ Δm.
  -- Substituting under the binder weakens the split across the two bound
  -- slots x,y (split-++ˡ / split-++ʳ); (A ∷ B ∷ []) ++ Δm and friends all
  -- reduce definitionally.
  sub-match⊗ˡ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} → Split-++ Γm (Ψ ++ Δm) s
              → Tm Ψ (A ⊗ B) → Tm (Γm ++ A ∷ B ∷ Δm) C → Tm Γ x
              → Tm (Θ ++ Γ ++ Ξ) C
  sub-match⊗ʳ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} → Split-++ Ψ Δm s'
              → Γm ++ Θ₂ ≡ Θ
              → Tm Ψ (A ⊗ B) → Tm (Γm ++ A ∷ B ∷ Δm) C → Tm Γ x
              → Tm (Θ ++ Γ ++ Ξ) C

  -- match𝟙(P, Q)[M/x]: as for match⊗, but with no bound slots.
  sub-match𝟙ˡ : {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ} → Split-++ Γm (Ψ ++ Δm) s
              → Tm Ψ 𝟙 → Tm (Γm ++ Δm) C → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) C
  sub-match𝟙ʳ : {s' : Split x Θ₂ (Ψ ++ Δm) Ξ} → Split-++ Ψ Δm s'
              → Γm ++ Θ₂ ≡ Θ
              → Tm Ψ 𝟙 → Tm (Γm ++ Δm) C → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) C

  -- (t ∷ ts)[M/x]: the slot is in the head xor in the tail.
  sub-cons : ∀ {A} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} → Split-++ Γ₁ Δ₁ s
           → Tm Γ₁ (base A) → Sp Δ₁ As → Tm Γ x → Sp (Θ ++ Γ ++ Ξ) (A ∷ As)

  sub s var             g = sub-var s g
  sub s (gen f sp)      g = gen f (sub-sp s sp g)
  sub s (⦅_,_⦆ {Γ = Γ₁} P Q) g = sub-pair (split-++ Γ₁ s) P Q g
  sub s (match⊗ {Γ = Γm} P Q) g = sub-match⊗ˡ (split-++ Γm s) P Q g
  sub s ⋆               g = absurd (split-[] s)
  sub s (match𝟙 {Γ = Γm} P Q) g = sub-match𝟙ˡ (split-++ Γm s) P Q g

  sub-sp s []                g = absurd (split-[] s)
  sub-sp s (_∷_ {Γ = Γ₁} t ts) g = sub-cons (split-++ Γ₁ s) t ts g

  sub-pair {Θ = Θ} {Δ₁ = Δ₁} {Ξ = Ξ} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q g =
    cast (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
      ⦅ sub s₁ P g , Q ⦆
  sub-pair {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) P Q g =
    cast (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
      ⦅ P , sub s₂ Q g ⦆

  sub-match⊗ˡ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {Ξ = Ξ} {A = A} {B = B} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q g =
    cast (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
      (match⊗ {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P
        (cast (sym (flattenˡ Θ Γ Ξ₁ (A ∷ B ∷ Δm)))
          (sub (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q g)))
  sub-match⊗ˡ {Ψ = Ψ} (on-right s' q _) P Q g =
    sub-match⊗ʳ (split-++ Ψ s') q P Q g

  sub-match⊗ʳ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p _) q P Q g =
    cast (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
      (match⊗ {Γ = Γm} {Δ = Δm} (sub s₁ P g) Q)
  sub-match⊗ʳ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {A = A} {B = B} {Γ = Γ}
    (on-right {Θ₂ = Θ₃} s₂ q₂ _) q P Q g =
    cast (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
      (match⊗ {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P
        (cast (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) Γ Ξ))
          (sub (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q g)))

  sub-match𝟙ˡ {Θ = Θ} {Ψ = Ψ} {Δm = Δm} {Ξ = Ξ} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p _) P Q g =
    cast (flattenˡ Θ Γ Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
      (match𝟙 {Γ = Θ ++ Γ ++ Ξ₁} {Δ = Δm} P
        (cast (sym (flattenˡ Θ Γ Ξ₁ Δm))
          (sub (split-++ˡ s₁ Δm) Q g)))
  sub-match𝟙ˡ {Ψ = Ψ} (on-right s' q _) P Q g =
    sub-match𝟙ʳ (split-++ Ψ s') q P Q g

  sub-match𝟙ʳ {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm} {Γ = Γ}
    (on-left {Ξ₁ = Ξ₁} s₁ p _) q P Q g =
    cast (flattenᵐ Γm Θ₂ Γ Ξ₁ Δm ∙ λ i → q i ++ Γ ++ p i)
      (match𝟙 {Γ = Γm} {Δ = Δm} (sub s₁ P g) Q)
  sub-match𝟙ʳ {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm} {Γ = Γ}
    (on-right {Θ₂ = Θ₃} s₂ q₂ _) q P Q g =
    cast (bury Γm Ψ Θ₃ (Γ ++ Ξ) ∙ ap (_++ Γ ++ Ξ) (ap (Γm ++_) q₂ ∙ q))
      (match𝟙 {Γ = Γm} {Δ = Θ₃ ++ Γ ++ Ξ} P
        (cast (sym (flattenʳ Γm Θ₃ Γ Ξ))
          (sub (split-++ʳ Γm s₂) Q g)))

  sub-cons {Θ = Θ} {Δ₁ = Δ₁} {Ξ = Ξ} {Γ = Γ} (on-left {Ξ₁ = Ξ₁} s₁ p _) t ts g =
    sp-cast (flattenˡ Θ Γ Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ Γ ++ Ξ') p)
      (sub s₁ t g ∷ ts)
  sub-cons {Γ₁ = Γ₁} {Ξ = Ξ} {Γ = Γ} (on-right {Θ₂ = Θ₂} s₂ q _) t ts g =
    sp-cast (flattenʳ Γ₁ Θ₂ Γ Ξ ∙ ap (λ Θ' → Θ' ++ Γ ++ Ξ) q)
      (t ∷ sub-sp s₂ ts g)

  -- ==========================================================================
  -- The β/η-congruence (§2.4.2, p. 109).  Only the raw generating relation:
  -- the set quotient supplies reflexivity/symmetry/transitivity, and the
  -- congruence rules make the term formers descend.  Context bookkeeping:
  -- η⊗, β𝟙 and η𝟙 are *homogeneous* (their boundaries agree definitionally,
  -- because ++ computes on the literal lists A ∷ B ∷ [] and []); only β⊗
  -- needs a cast, along the structural boundary below — precisely the
  -- pattern of assocₘ in Multicategory.agda.
  -- ==========================================================================

  --   (Γm ++ Γ₁) ++ Δ₁ ++ Δm ≡ Γm ++ (Γ₁ ++ Δ₁) ++ Δm
  β⊗-boundary : ∀ (Γm Γ₁ Δ₁ Δm : Ctx) → (Γm ++ Γ₁) ++ Δ₁ ++ Δm ≡ Γm ++ (Γ₁ ++ Δ₁) ++ Δm
  β⊗-boundary = LP.pivot

  data _≈_  : Tm Γ z → Tm Γ z → Type (o ⊔ h)
  data _≈ₛ_ : Sp Γ As → Sp Γ As → Type (o ⊔ h)

  data _≈_ where
    -- equivalence closure (the set quotient would supply this anyway, but
    -- having it inside _≈_ lets Tm-level proofs chain β/η steps, and gives
    -- the reflexivity Quot-op₂ requires when descending sub)
    ≈-refl  : {t : Tm Γ z} → t ≈ t
    ≈-sym   : {t t' : Tm Γ z} → t ≈ t' → t' ≈ t
    ≈-trans : {t t' t'' : Tm Γ z} → t ≈ t' → t' ≈ t'' → t ≈ t''

    -- congruence
    gen-cong : ∀ {B} {f : G.Hom As B} {ss ss' : Sp Γ As}
             → ss ≈ₛ ss' → gen f ss ≈ gen f ss'
    ⦅,⦆-cong : {M M' : Tm Γ A} {N N' : Tm Δ B}
             → M ≈ M' → N ≈ N' → ⦅ M , N ⦆ ≈ ⦅ M' , N' ⦆
    match⊗-cong : {M M' : Tm Ψ (A ⊗ B)} {N N' : Tm (Γ ++ A ∷ B ∷ Δ) C}
                → M ≈ M' → N ≈ N'
                → match⊗ {Γ = Γ} {Δ = Δ} M N ≈ match⊗ {Γ = Γ} {Δ = Δ} M' N'
    match𝟙-cong : {M M' : Tm Ψ 𝟙} {N N' : Tm (Γ ++ Δ) C}
                → M ≈ M' → N ≈ N'
                → match𝟙 {Γ = Γ} {Δ = Δ} M N ≈ match𝟙 {Γ = Γ} {Δ = Δ} M' N'

    -- match⊗(⦅M,N⦆, xy.P) ≡ P[M/x, N/y]
    β⊗ : ∀ {Γm Δm Γ₁ Δ₁} (M : Tm Γ₁ A) (N : Tm Δ₁ B) (P : Tm (Γm ++ A ∷ B ∷ Δm) C)
       → match⊗ {Γ = Γm} {Δ = Δm} ⦅ M , N ⦆ P
       ≈ cast (β⊗-boundary Γm Γ₁ Δ₁ Δm)
           (sub (split-++ʳ Γm (split-here Γ₁ B Δm))
                (sub (split-here Γm A (B ∷ Δm)) P M) N)

    -- match⊗(M, xy.N[⦅x,y⦆/u]) ≡ N[M/u]
    η⊗ : ∀ {Γm Δm} (M : Tm Ψ (A ⊗ B)) (N : Tm (Γm ++ (A ⊗ B) ∷ Δm) C)
       → match⊗ {Γ = Γm} {Δ = Δm} M
           (sub (split-here Γm (A ⊗ B) Δm) N ⦅ var , var ⦆)
       ≈ sub (split-here Γm (A ⊗ B) Δm) N M

    -- match𝟙(⋆, N) ≡ N
    β𝟙 : ∀ {Γm Δm} (N : Tm (Γm ++ Δm) C)
       → match𝟙 {Ψ = []} {Γ = Γm} {Δ = Δm} ⋆ N ≈ N

    -- match𝟙(M, N[⋆/u]) ≡ N[M/u]
    η𝟙 : ∀ {Γm Δm} (M : Tm Ψ 𝟙) (N : Tm (Γm ++ 𝟙 ∷ Δm) C)
       → match𝟙 {Γ = Γm} {Δ = Δm} M (sub (split-here Γm 𝟙 Δm) N ⋆)
       ≈ sub (split-here Γm 𝟙 Δm) N M

  data _≈ₛ_ where
    nil  : _≈ₛ_ {Γ = []} [] []
    cons : ∀ {A} {t t' : Tm Γ (base A)} {ts ts' : Sp Δ As}
         → t ≈ t' → ts ≈ₛ ts' → (t ∷ ts) ≈ₛ (t' ∷ ts')

  -- The hom-sets of the syntactic multicategory FMonCat G (Theorem 2.4.10):
  -- terms modulo the congruence generated by β/η.
  Homₘ : Ctx → Ty → Type (o ⊔ h)
  Homₘ Γ z = Tm Γ z / _≈_

  idₘ : Homₘ (z ∷ []) z
  idₘ = inc var

  -- Where the rest of the development lives (all formalised):
  --  1. sub respects _≈_ in both arguments — Free/CongruenceLeft,
  --     Free/CongruenceRight (β/η cases: Free/RedexStability) — so sub
  --     descends to _∘ₘ_ via Quot-op₂.
  --  2. The Premulticategory laws for sub — Free/Identity, Free/Assoc,
  --     Free/Interchange — assembled into FMonCat G : Premulticategory in
  --     Free/Multicategory (on the shared kit Free/Kit, Free/SplitLemmas).
  --  3. Representability of FMonCat G (⦅var,var⦆/⋆ universal via the β/η
  --     round-trips, n-ary arrows by induction) — Free/Representable;
  --     Free/Strict feeds it through Multicategory.Strictification.
  --  4. Freeness (Theorem 2.4.10): evaluation into any representable
  --     premulticategory — Free/Eval; it maps sub to _∘ₘ_, respects _≈_,
  --     and descends to a multifunctor — Free/Freeness; uniqueness of the
  --     extension — Free/Uniqueness.
