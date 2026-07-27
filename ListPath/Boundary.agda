-- Uniform generation of structural list-reassociation boundaries.
--
-- Every boundary path in the multicategory signature (slot-unbury,
-- interchange-slot₁, flattenˡ, bury, buryᵐ, pivot, …) is an instance of ONE
-- fact: any two bracketings of the same sequence of list- and element-slots
-- are connected by a canonical cons-by-cons path.  This module implements
-- that fact as an elaboration-time NbE: `declare-boundary` takes the two
-- bracketing SHAPES, symbolically peels their common frontier left to right
-- (dropping exhausted atoms definitionally, crossing element slots under an
-- `ap`-cons, stopping with refl as soon as the residual shapes coincide),
-- and EMITS the resulting recursion as an ordinary definition built from
-- 1lab's `List-elim` and `ap (x ∷_)`.  The emitted path is ∙-free and cons-headed
-- under every concrete cons — the structural discipline of
-- Multicategory.agda — and closed instances reduce to refl.
--
-- Why elaboration time and not a value-level `path-of`?  A term-level
-- function generic in the bracketing codes cannot expose the head of the
-- interpretation under an ABSTRACT code (⟦B⟧((x ∷ Γ), ρ) ≐ x ∷ ⟦B⟧(Γ, ρ)
-- only computes when B's constructors are visible), so the generic path can
-- only be assembled through propositional peel lemmas joined by _∙_ — and
-- cubical _∙_ is an hcomp that folds like ⊗-context cannot see through,
-- even at refl.  Running the same NbE over the (always concrete) shapes at
-- elaboration time reifies its trace as a bona fide structural recursion
-- instead, keeping every definitional property the codebase relies on.
--
-- Scope: ε-free reassociation boundaries (no [] literals in the shapes) —
-- exactly the family that feeds the Premulticategory laws.  Unit
-- coherences (++-idr instances) stay with ListPath.Solver.
module ListPath.Boundary where

open import 1Lab.Type
open import 1Lab.Path
open import Data.List
open import Data.Bool
open import 1Lab.Reflection
open import 1Lab.Reflection.Subst using (raise)

-- The recursion engine of every generated boundary is 1lab's List-elim
-- (Data.List.Base): generated terms contain no self-reference, so the
-- termination checker never sees a recursive definition.

-- ==========================================================================
-- Shapes: bracketing trees over a frontier of list slots (●) and element
-- slots (◆).  ◆ ⊛ S interprets as x ∷ ⟦S⟧, so shapes denote exactly the
-- ++/∷-terms the boundaries are stated with.
-- ==========================================================================

data Sh : Type where
  ●   : Sh
  ◆   : Sh
  _⊛_ : Sh → Sh → Sh

infixr 30 _⊛_

data Kind : Type where
  lst el : Kind

frontier : Sh → List Kind
frontier ●       = lst ∷ []
frontier ◆       = el ∷ []
frontier (s ⊛ t) = frontier s ++ frontier t

private
  kind-eq : Kind → Kind → Bool
  kind-eq lst lst = true
  kind-eq el  el  = true
  kind-eq _   _   = false

  kinds-eq : List Kind → List Kind → Bool
  kinds-eq []       []       = true
  kinds-eq (k ∷ ks) (l ∷ ls) = if kind-eq k l then kinds-eq ks ls else false
  kinds-eq _        _        = false

  sh-eq : Sh → Sh → Bool
  sh-eq ●         ●         = true
  sh-eq ◆         ◆         = true
  sh-eq (s ⊛ t)   (s' ⊛ t') = if sh-eq s s' then sh-eq t t' else false
  sh-eq _         _         = false

  head-kind : Sh → Kind
  head-kind ●       = lst
  head-kind ◆       = el
  head-kind (s ⊛ _) = head-kind s

  -- Remove the leftmost leaf.  The interpretation of the result is
  -- DEFINITIONALLY the interpretation of the original at [] (for ●: the
  -- head [] computes through every ++ on the left spine) resp. under the
  -- peeled head (for ◆).
  drop₁ : Sh → Maybe Sh
  drop₁ ●       = nothing
  drop₁ ◆       = nothing
  drop₁ (s ⊛ t) with drop₁ s
  ... | just s' = just (s' ⊛ t)
  ... | nothing = just t

  drop! : Sh → TC Sh
  drop! s with drop₁ s
  ... | just s' = pure s'
  ... | nothing = typeError (strErr "declare-boundary: internal drop of a leaf" ∷ [])

  -- ------------------------------------------------------------------------
  -- Term builders.
  -- ------------------------------------------------------------------------

  cons-tm : Term → Term → Term
  cons-tm x xs = con (quote List._∷_) (x v∷ xs v∷ [])

  nil-tm : Term
  nil-tm = con (quote List.[]) []

  append-tm : Term → Term → Term
  append-tm xs ys = def (quote _++_) (unknown h∷ unknown h∷ xs v∷ ys v∷ [])

  path-ty : Term → Term → Term
  path-ty l r = def (quote _≡_) (unknown h∷ unknown h∷ l v∷ r v∷ [])

  ap-tm : Term → Term → Term
  ap-tm f p = def (quote ap)
    (unknown h∷ unknown h∷ unknown h∷ unknown h∷ f v∷ unknown h∷ unknown h∷ p v∷ [])

  -- (vlam comes from 1Lab.Reflection.)
  cons-lam : Term → Term
  cons-lam x = vlam "l" (cons-tm (raise 1 x) (var 0 []))

  -- ⟦S⟧ as a term, consuming the slot variables in frontier order.
  sh-term : Sh → List Term → Term × List Term
  sh-term ●       (t ∷ ts) = t , ts
  sh-term ◆       (t ∷ ts) = cons-tm t nil-tm , ts
  sh-term (◆ ⊛ s) (t ∷ ts) =
    let (u , ts') = sh-term s ts in cons-tm t u , ts'
  sh-term (s ⊛ t) ts =
    let (u , ts₁) = sh-term s ts
        (v , ts₂) = sh-term t ts₁
    in append-tm u v , ts₂
  sh-term _ [] = unknown , []

  sh-tm : Sh → List Term → Term
  sh-tm s ts = sh-term s ts .fst

  -- The cons step of every peel: λ a Γ ih → ap (a ∷_) ih.
  step-tm : Term
  step-tm =
    vlam "a" (vlam "Γ" (vlam "ih"
      (ap-tm (vlam "l" (cons-tm (var 3 []) (var 0 []))) (var 0 []))))

  -- ------------------------------------------------------------------------
  -- The NbE loop: symbolically peel the two shapes, emitting the path term.
  -- vs are the slot variables (frontier order) in the current context.
  -- ------------------------------------------------------------------------

  go    : Nat → Sh → Sh → List Term → TC Term
  go-ne : Nat → Kind → Sh → Sh → List Term → TC Term

  go zero _ _ _ = typeError (strErr "declare-boundary: fuel exhausted" ∷ [])
  go (suc n) s₁ s₂ vs with sh-eq s₁ s₂
  ... | true  = pure (def (quote refl) [])
  ... | false = go-ne n (head-kind s₁) s₁ s₂ vs

  -- Element slot in front: peel it under an ap-cons; residual shapes drop it.
  go-ne n el s₁ s₂ (x ∷ vs) = do
    s₁' ← drop! s₁
    s₂' ← drop! s₂
    rest ← go n s₁' s₂' vs
    pure (ap-tm (cons-lam x) rest)
  -- List slot in front: eliminate it.  The base (slot := []) converts to the
  -- dropped shapes; the cons case is the uniform ap-cons step.
  go-ne n lst s₁ s₂ (x ∷ vs) = do
    s₁' ← drop! s₁
    s₂' ← drop! s₂
    base ← go n s₁' s₂' vs
    let vs' = var 0 [] ∷ map (raise 1) vs
        motive = vlam "Γ" (path-ty (sh-tm s₁ vs') (sh-tm s₂ vs'))
    pure (def (quote List-elim)
      (unknown h∷ unknown h∷ unknown h∷ motive v∷ base v∷ step-tm v∷ x v∷ []))
  go-ne _ _ _ _ [] =
    typeError (strErr "declare-boundary: slot variables exhausted" ∷ [])

  -- ------------------------------------------------------------------------
  -- Declaration: ∀ {ℓ} {A : Type ℓ} (x₁ : τ₁) … (xₙ : τₙ) → ⟦S₁⟧ ≡ ⟦S₂⟧.
  -- ------------------------------------------------------------------------

  count-down : Nat → List Nat
  count-down zero    = []
  count-down (suc n) = n ∷ count-down n

  slot-vars : Nat → List Term
  slot-vars n = map (λ k → var k []) (count-down n)

  arg-ty : Kind → Nat → Term
  arg-ty lst iA = def (quote List) (unknown h∷ var iA [] v∷ [])
  arg-ty el  iA = var iA []

  make-ty : List Kind → Sh → Sh → Term
  make-ty ks s₁ s₂ =
    pi (argH (def (quote Level) [])) (abs "ℓ"
      (pi (argH (def (quote Type) (var 0 [] v∷ []))) (abs "A"
        (go-pis 0 ks))))
    where
      n = length ks
      go-pis : Nat → List Kind → Term
      go-pis j [] =
        let vs = slot-vars n
        in path-ty (sh-tm s₁ vs) (sh-tm s₂ vs)
      go-pis j (k ∷ ks') =
        pi (argN (arg-ty k j)) (abs "x" (go-pis (suc j) ks'))

  -- The clause telescope mirroring make-ty ({ℓ} {A} then the slots).
  make-tel : List Kind → Telescope
  make-tel ks =
    ("ℓ" , argH (def (quote Level) [])) ∷
    ("A" , argH (def (quote Type) (var 0 [] v∷ []))) ∷
    go-tel 0 ks
    where
      go-tel : Nat → List Kind → Telescope
      go-tel j []        = []
      go-tel j (k ∷ ks') = ("x" , argN (arg-ty k j)) ∷ go-tel (suc j) ks'

-- Declare and define a boundary from its two shapes.  Usage:
--   unquoteDecl slot-unbury = declare-boundary slot-unbury
--     (● ⊛ ((● ⊛ (◆ ⊛ ●)) ⊛ ●)) ((● ⊛ ●) ⊛ (◆ ⊛ (● ⊛ ●)))
declare-boundary : Name → Sh → Sh → TC ⊤
declare-boundary nm s₁ s₂ with kinds-eq (frontier s₁) (frontier s₂)
... | false = typeError (strErr "declare-boundary: shapes have different frontiers" ∷ [])
... | true  = do
  let ks  = frontier s₁
      tel = make-tel ks
  declare (argN nm) (make-ty ks s₁ s₂)
  core ← go (suc (length ks)) s₁ s₂ (slot-vars (length ks))
  define-function nm (clause tel (tel→pats 0 tel) core ∷ [])

-- ==========================================================================
-- Tests: regenerate the multicategory boundary family and check the
-- definitional properties the codebase relies on.
-- ==========================================================================

private module Test {ℓ} {A : Type ℓ} where
  -- ++-assoc's shape.
  unquoteDecl assoc′ = declare-boundary assoc′
    ((● ⊛ ●) ⊛ ●) (● ⊛ (● ⊛ ●))

  _ : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  _ = assoc′

  -- slot-unbury: Θ ++ ((Φ ++ x ∷ Ψ) ++ Ξ) ≡ (Θ ++ Φ) ++ x ∷ (Ψ ++ Ξ).
  unquoteDecl slot-unbury′ = declare-boundary slot-unbury′
    (● ⊛ ((● ⊛ (◆ ⊛ ●)) ⊛ ●)) ((● ⊛ ●) ⊛ (◆ ⊛ (● ⊛ ●)))

  _ : (Θ Φ : List A) (x : A) (Ψ Ξ : List A)
    → Θ ++ ((Φ ++ x ∷ Ψ) ++ Ξ) ≡ (Θ ++ Φ) ++ x ∷ (Ψ ++ Ξ)
  _ = slot-unbury′

  -- flattenˡ: (xs ++ ys ++ zs) ++ ws ≡ xs ++ ys ++ (zs ++ ws).
  unquoteDecl flattenˡ′ = declare-boundary flattenˡ′
    ((● ⊛ (● ⊛ ●)) ⊛ ●) (● ⊛ (● ⊛ (● ⊛ ●)))

  _ : (xs ys zs ws : List A) → (xs ++ ys ++ zs) ++ ws ≡ xs ++ ys ++ (zs ++ ws)
  _ = flattenˡ′

  -- interchange-slot₁: Θ ++ Γ ++ Μ ++ y ∷ Κ ≡ (Θ ++ Γ ++ Μ) ++ y ∷ Κ.
  unquoteDecl ic-slot₁′ = declare-boundary ic-slot₁′
    (● ⊛ (● ⊛ (● ⊛ (◆ ⊛ ●)))) ((● ⊛ (● ⊛ ●)) ⊛ (◆ ⊛ ●))

  _ : (Θ Γ Μ : List A) (y : A) (Κ : List A)
    → Θ ++ Γ ++ Μ ++ y ∷ Κ ≡ (Θ ++ Γ ++ Μ) ++ y ∷ Κ
  _ = ic-slot₁′

  -- buryᵐ, the deepest boundary in the assocₘ law.
  unquoteDecl buryᵐ′ = declare-boundary buryᵐ′
    ((● ⊛ ●) ⊛ (● ⊛ (● ⊛ ●))) (● ⊛ ((● ⊛ (● ⊛ ●)) ⊛ ●))

  _ : (Θ Φ Ρ Ψ Ξ : List A)
    → (Θ ++ Φ) ++ Ρ ++ (Ψ ++ Ξ) ≡ Θ ++ ((Φ ++ Ρ ++ Ψ) ++ Ξ)
  _ = buryᵐ′

  -- The structural discipline: cons-by-cons reduction is DEFINITIONAL.
  _ : (a : A) (Θ Φ : List A) (x : A) (Ψ Ξ : List A)
    → slot-unbury′ (a ∷ Θ) Φ x Ψ Ξ ≡ ap (a ∷_) (slot-unbury′ Θ Φ x Ψ Ξ)
  _ = λ a Θ Φ x Ψ Ξ → refl

  -- Closed instances are definitionally refl (no transport/hcomp residue).
  _ : (a b x c d : A)
    → slot-unbury′ (a ∷ []) (b ∷ []) x (c ∷ []) (d ∷ []) ≡ refl
  _ = λ a b x c d → refl

  -- The generated assoc agrees with 1lab's ++-assoc definitionally at every
  -- constructor, hence propositionally everywhere (two-line induction).
  assoc′-is-++-assoc : (xs ys zs : List A) → assoc′ xs ys zs ≡ ++-assoc xs ys zs
  assoc′-is-++-assoc []       ys zs = refl
  assoc′-is-++-assoc (x ∷ xs) ys zs = ap (ap (x ∷_)) (assoc′-is-++-assoc xs ys zs)
