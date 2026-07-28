-- The tensor interpretation of bracketing shapes: for any monoidal
-- category, a shape S over the ListPath.Boundary frontier denotes both a
-- context (⟦S⟧ˡ, the ++/∷-term the boundaries are stated with) and a
-- tensor expression (⟦S⟧⊗, with ⊗-context wrapped around list slots, bare
-- objects at element slots, and ⊗ following the shape's bracketing), and
-- the canonical comparison
--
--   iso-of S ρ : ⊗-context (⟦S⟧ˡ ρ) ≅ ⟦S⟧⊗ ρ
--
-- is generated uniformly by a fold over the shape.  E.g.
--
--   iso-of (● ⊛ (◆ ⊛ ●)) : ⊗-context (ys₁ ++ y ∷ ys₂)
--                        ≅ ⊗-context ys₁ ⊗ (y ⊗ ⊗-context ys₂).
--
-- Unlike the boundary PATHS (which must be emitted at elaboration time so
-- they stay ∙-free and cons-headed), this layer is a plain value-level
-- function: isos compose freely, and every definitional reduction it
-- needs is directed by the shape's constructors — ⟦S⟧ˡ is cons- or
-- ++-headed by construction, so ⊗-context always computes one step per
-- clause.  The only inductive-on-lists content is the binary comparison
-- ⊗-context-++, stated once.
module ListPath.Tensor where

open import 1Lab.Prelude hiding (id; _∘_)
open import Cat.Base
import Cat.Reasoning as Cr
open import Cat.Monoidal.Base
open import Data.List

open import ListPath.Boundary using (Sh; ●; ◆; _⊛_; Kind; lst; el; frontier)

module Tensor {o h} {C : Precategory o h} (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M

  ⊗-context : List Ob → Ob
  ⊗-context []      = Unit
  ⊗-context (x ∷ Γ) = x ⊗ ⊗-context Γ

  -- The binary comparison: tensor of a concatenation splits into the
  -- tensors of the parts.  Reducing (cons-by-cons on Γ).
  ⊗-context-++ : (Γ Δ : List Ob)
    → ⊗-context (Γ ++ Δ) ≅ (⊗-context Γ ⊗ ⊗-context Δ)
  ⊗-context-++ []      Δ = λ≅
  ⊗-context-++ (x ∷ Γ) Δ = ▶.F-map-iso (⊗-context-++ Γ Δ) ∙Iso (α≅ Iso⁻¹)

  -- Functorial image of a pair of isos under ⊗.
  _⊗ᵢ_ : ∀ {a b c d} → a ≅ b → c ≅ d → (a ⊗ c) ≅ (b ⊗ d)
  f ⊗ᵢ g = ◀.F-map-iso f ∙Iso ▶.F-map-iso g

  -- ------------------------------------------------------------------------
  -- Environments over a frontier, and the two interpretations of a shape.
  -- ------------------------------------------------------------------------

  Env : List Kind → Type o
  Env []         = Lift o ⊤
  Env (lst ∷ ks) = List Ob × Env ks
  Env (el  ∷ ks) = Ob × Env ks

  env-split : ∀ ks₁ {ks₂} → Env (ks₁ ++ ks₂) → Env ks₁ × Env ks₂
  env-split []          ρ       = lift tt , ρ
  env-split (lst ∷ ks₁) (Γ , ρ) =
    let (ρ₁ , ρ₂) = env-split ks₁ ρ in (Γ , ρ₁) , ρ₂
  env-split (el ∷ ks₁)  (y , ρ) =
    let (ρ₁ , ρ₂) = env-split ks₁ ρ in (y , ρ₁) , ρ₂

  -- The context a shape denotes.  Clauses split ⊛ by its LEFT constructor
  -- so they are non-overlapping — every ⟦S⟧ˡ reduces as soon as the
  -- shape's constructors are exposed, and element slots become literal
  -- conses, so ⟦S⟧ˡ is syntactically the ++/∷-term of the boundary
  -- statements.
  ⟦_⟧ˡ : (S : Sh) → Env (frontier S) → List Ob
  ⟦ ● ⟧ˡ              (Γ , _) = Γ
  ⟦ ◆ ⟧ˡ              (y , _) = y ∷ []
  ⟦ ● ⊛ S ⟧ˡ          (Γ , ρ) = Γ ++ ⟦ S ⟧ˡ ρ
  ⟦ ◆ ⊛ S ⟧ˡ          (y , ρ) = y ∷ ⟦ S ⟧ˡ ρ
  ⟦ (S₁ ⊛ S₂) ⊛ S₃ ⟧ˡ ρ =
    let (ρ₁ , ρ₂) = env-split (frontier (S₁ ⊛ S₂)) ρ
    in ⟦ S₁ ⊛ S₂ ⟧ˡ ρ₁ ++ ⟦ S₃ ⟧ˡ ρ₂

  -- The tensor expression a shape denotes, bracketed like the shape.
  ⟦_⟧⊗ : (S : Sh) → Env (frontier S) → Ob
  ⟦ ● ⟧⊗              (Γ , _) = ⊗-context Γ
  ⟦ ◆ ⟧⊗              (y , _) = y
  ⟦ ● ⊛ S ⟧⊗          (Γ , ρ) = ⊗-context Γ ⊗ ⟦ S ⟧⊗ ρ
  ⟦ ◆ ⊛ S ⟧⊗          (y , ρ) = y ⊗ ⟦ S ⟧⊗ ρ
  ⟦ (S₁ ⊛ S₂) ⊛ S₃ ⟧⊗ ρ =
    let (ρ₁ , ρ₂) = env-split (frontier (S₁ ⊛ S₂)) ρ
    in ⟦ S₁ ⊛ S₂ ⟧⊗ ρ₁ ⊗ ⟦ S₃ ⟧⊗ ρ₂

  -- ------------------------------------------------------------------------
  -- The generic comparison.
  -- ------------------------------------------------------------------------

  iso-of : (S : Sh) (ρ : Env (frontier S)) → ⊗-context (⟦ S ⟧ˡ ρ) ≅ ⟦ S ⟧⊗ ρ
  iso-of ●                 ρ       = id-iso
  iso-of ◆                 (y , _) = ρ≅ Iso⁻¹
  iso-of (● ⊛ S)           (Γ , ρ) =
    ⊗-context-++ Γ (⟦ S ⟧ˡ ρ) ∙Iso ▶.F-map-iso (iso-of S ρ)
  iso-of (◆ ⊛ S)           (y , ρ) = ▶.F-map-iso (iso-of S ρ)
  iso-of ((S₁ ⊛ S₂) ⊛ S₃) ρ =
    let (ρ₁ , ρ₂) = env-split (frontier (S₁ ⊛ S₂)) ρ
    in ⊗-context-++ (⟦ S₁ ⊛ S₂ ⟧ˡ ρ₁) (⟦ S₃ ⟧ˡ ρ₂)
       ∙Iso (iso-of (S₁ ⊛ S₂) ρ₁ ⊗ᵢ iso-of S₃ ρ₂)

  -- ------------------------------------------------------------------------
  -- Tests: the shapes of the multicategory instance.
  -- ------------------------------------------------------------------------

  private
    -- The motivating example: expose a marked slot.
    _ : (ys₁ : List Ob) (y : Ob) (ys₂ : List Ob)
      → ⊗-context (ys₁ ++ y ∷ ys₂) ≅ (⊗-context ys₁ ⊗ (y ⊗ ⊗-context ys₂))
    _ = λ ys₁ y ys₂ → iso-of (● ⊛ (◆ ⊛ ●)) (ys₁ , y , ys₂ , _)

    -- Binary and ternary splits.
    _ : (Γ Δ : List Ob) → ⊗-context (Γ ++ Δ) ≅ (⊗-context Γ ⊗ ⊗-context Δ)
    _ = λ Γ Δ → iso-of (● ⊛ ●) (Γ , Δ , lift tt)

    _ : (Γ Δ Ξ : List Ob)
      → ⊗-context (Γ ++ Δ ++ Ξ)
      ≅ (⊗-context Γ ⊗ (⊗-context Δ ⊗ ⊗-context Ξ))
    _ = λ Γ Δ Ξ → iso-of (● ⊛ (● ⊛ ●)) (Γ , Δ , Ξ , lift tt)

    -- A two-slot interchange-style shape.
    _ : (xs₁ : List Ob) (x₁ : Ob) (xs₂ : List Ob) (x₂ : Ob) (xs₃ : List Ob)
      → ⊗-context (xs₁ ++ x₁ ∷ xs₂ ++ x₂ ∷ xs₃)
      ≅ (⊗-context xs₁ ⊗ (x₁ ⊗ (⊗-context xs₂ ⊗ (x₂ ⊗ ⊗-context xs₃))))
    _ = λ xs₁ x₁ xs₂ x₂ xs₃ →
      iso-of (● ⊛ (◆ ⊛ (● ⊛ (◆ ⊛ ●)))) (xs₁ , x₁ , xs₂ , x₂ , xs₃ , lift tt)

  -- ------------------------------------------------------------------------
  -- The goal-directed interface: `tensor!` reads the ⊗-side of the goal,
  -- reconstructs the shape (⊗-context ↦ ●, plain object ↦ ◆, ⊗ ↦ ⊛) and
  -- the environment, and applies iso-of.  Unifying the result against the
  -- goal checks the context side, so no separate soundness step is needed.
  -- ------------------------------------------------------------------------

  module Reflect where
    open import 1Lab.Reflection
    open import 1Lab.Reflection.Subst using (apply-tm*)

    last-vis : List (Arg Term) → Maybe Term
    last-vis = go nothing where
      go : Maybe Term → List (Arg Term) → Maybe Term
      go acc []                                = acc
      go acc (arg (arginfo visible _) t ∷ as)  = go (just t) as
      go acc (_ ∷ as)                          = go acc as

    _,ᵗ_ : Term → Term → Term
    x ,ᵗ ρ = con (quote _,_) (x v∷ ρ v∷ [])

    name-eq : Name → Name → Bool
    name-eq n m = Dec-rec (λ _ → true) (λ _ → false) (n ≡? m)

    -- Parse a tensor expression into (shape, environment-with-hole).
    --
    -- Scope caveat: every `open Monoidal-category M` / `open Tensor M` site
    -- mints its own definitionally-equal COPIES of _⊗_ and ⊗-context, so
    -- syntactic name-matching against this module's names fails at client
    -- sites.  ⊗ is matched UP TO CONVERSION (speculative unification with
    -- ?a ⊗ ?b — the metas land in rigid pair positions, so this solves);
    -- ⊗-context cannot be matched that way (unifying under a defined
    -- function blocks), but whnf unfolds any copy back to the ORIGINAL
    -- definition, whose name we can match.  (TERMINATING: the recursion
    -- goes through solved metas.)
    {-# TERMINATING #-}
    parse : Term → TC (Term × (Term → Term))
    parse-atom : Term → Term → TC (Term × (Term → Term))

    parse t = do
      `Ob ← quoteTC Ob
      `f ← quoteTC (λ (x y : Ob) → x ⊗ y)
      -- Metas are created INSIDE the speculation, so a failed attempt
      -- rolls them back rather than leaving them unsolved.
      r ← (noConstraints (do
              a ← new-meta `Ob
              b ← new-meta `Ob
              unify t (apply-tm* `f (argN a ∷ argN b ∷ []))
              a' ← reduce a
              b' ← reduce b
              pure (just (a' , b'))))
            <|> pure nothing
      case r of λ where
        (just (a , b)) → do
          (S₁ , κ₁) ← parse a
          (S₂ , κ₂) ← parse b
          pure (con (quote _⊛_) (S₁ v∷ S₂ v∷ []) , λ u → κ₁ (κ₂ u))
        nothing → do
          t' ← reduce t
          parse-atom t t'

    parse-atom t (def n as) with name-eq n (quote ⊗-context) | last-vis as
    ... | true  | just Γ = pure (con (quote ●) [] , (Γ ,ᵗ_))
    ... | _     | _      = pure (con (quote ◆) [] , (t ,ᵗ_))
    parse-atom t _ = pure (con (quote ◆) [] , (t ,ᵗ_))

    macro
      tensor! : Term → TC ⊤
      tensor! goal = do
        ty ← wait-for-type =<< infer-type goal
        def _ as ← pure ty
          where t → typeError (strErr "tensor!: goal is not an isomorphism\n  " ∷ termErr t ∷ [])
        just rhs ← pure (last-vis as)
          where _ → typeError (strErr "tensor!: goal is not an isomorphism" ∷ [])
        (S , κ) ← parse rhs
        `iso ← quoteTC iso-of
        unify goal (apply-tm* `iso (argN S ∷ argN (κ unknown) ∷ []))

  open Reflect using (tensor!) public

  private
    -- The macro interface: no arguments at all.
    _ : (ys₁ : List Ob) (y : Ob) (ys₂ : List Ob)
      → ⊗-context (ys₁ ++ y ∷ ys₂) ≅ (⊗-context ys₁ ⊗ (y ⊗ ⊗-context ys₂))
    _ = λ ys₁ y ys₂ → tensor!

    _ : (Γ Δ Ξ : List Ob)
      → ⊗-context (Γ ++ Δ ++ Ξ)
      ≅ (⊗-context Γ ⊗ (⊗-context Δ ⊗ ⊗-context Ξ))
    _ = λ Γ Δ Ξ → tensor!

    _ : (xs₁ : List Ob) (x₁ : Ob) (xs₂ : List Ob) (x₂ : Ob) (xs₃ : List Ob)
      → ⊗-context (xs₁ ++ x₁ ∷ xs₂ ++ x₂ ∷ xs₃)
      ≅ (⊗-context xs₁ ⊗ (x₁ ⊗ (⊗-context xs₂ ⊗ (x₂ ⊗ ⊗-context xs₃))))
    _ = λ xs₁ x₁ xs₂ x₂ xs₃ → tensor!
