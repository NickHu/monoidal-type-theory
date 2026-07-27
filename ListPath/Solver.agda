open import 1Lab.Prelude
open import Data.List
open import Data.List.Properties

-- Coherence solver for structural paths between lists — complete, no holes,
-- no postulates.  Three layers:
--   Tier A    explicit codes: solve / over (PathP rebasing)
--   Tier 1.5  the cast calculus: module Cast (CExp towers, fuse, reduce,
--             solve-cast)
--   Tier B    the list! macro: quotes both sides of a `p ≡ q` goal and
--             synthesises the residue premise via the collapse-* combinators
-- Cat.Bi.Solver is the blueprint, with its atom-commuting machinery
-- (Frame/frame-compare/Val₂) deleted: our 2-cell syntax PExp has no
-- opaque-path atoms, so every cell normalises to the canonical one.
--
-- Design summary
--   LExp        formal list expressions; atoms are opaque lists [ xs ] and
--               opaque elements x ∷ᵉ_ (pointed decompositions xs ++ x ∷ ys
--               mix both).
--   eval        difference-list (Cayley) evaluation: eval (E₁ ⊕ E₂) κ =
--               eval E₁ (eval E₂ κ), so reassociation/unit laws of ⊕ hold
--               DEFINITIONALLY at the nf level even on open expressions.
--   PExp E₁ E₂  formal structural paths: refl/∙/sym, ap-cons, one-sided
--               whiskers, ++-assoc, ++-idr, plus one generator per NAMED
--               composite reassociation (flattenˡ …; these mirror the
--               boundary paths of the multicategory formalisation, which
--               should alias them — e.g. flattenˡ = ListPath.Solver.NbE.flattenˡ
--               — so its goals are in-vocabulary on the nose).
--   flatκ P κ   the residue of P at the nf level.  Because eval absorbs every
--               pure reassociation definitionally, flatκ is refl in every
--               generator clause; only ∙ᵖ produces a composite.  Hence at
--               concrete call sites the premise `flat P ≡ flat Q` is a
--               statement about composites of refl, discharged by refl or
--               ∙-idl/∙-idr one-liners (see the tests).
--   soundκ      every code's path fits in a square over its flat residue,
--               with the normalisation paths as the vertical sides (the
--               analogue of Cat.Bi.Solver's eval₂-sound).  Its leaves are
--               the seed coherences: sound-idr (triangle), sound-assoc
--               (pentagon), and one bridge per named reassociation.
--
-- Scope: pure structural squares between paths built from the grammar above.
-- Out of scope: PathPs of inductive witnesses over such paths (e.g. Split
-- values — keep those as 2-line cons inductions) and squares containing an
-- opaque path atom (would need the Frame machinery).

module ListPath.Solver where

module NbE {o} (X : Type o) where

  -- ==========================================================================
  -- §0  The named composite reassociations.  All cons-by-cons; clients that
  --     already have their own copies (e.g. Multicategory.Free) should alias
  --     them to these so the solver's vocabulary matches definitionally.
  -- ==========================================================================

  flattenˡ : ∀ (xs ys zs ws : List X)
           → (xs ++ ys ++ zs) ++ ws ≡ xs ++ ys ++ (zs ++ ws)
  flattenˡ []       ys zs ws = ++-assoc ys zs ws
  flattenˡ (x ∷ xs) ys zs ws = ap (x ∷_) (flattenˡ xs ys zs ws)

  flattenʳ : ∀ (xs ys zs ws : List X)
           → xs ++ (ys ++ zs ++ ws) ≡ (xs ++ ys) ++ zs ++ ws
  flattenʳ []       ys zs ws = refl
  flattenʳ (x ∷ xs) ys zs ws = ap (x ∷_) (flattenʳ xs ys zs ws)

  flattenᵐ : ∀ (xs ys zs ws us : List X)
           → xs ++ ((ys ++ zs ++ ws) ++ us) ≡ (xs ++ ys) ++ zs ++ (ws ++ us)
  flattenᵐ []       ys zs ws us = flattenˡ ys zs ws us
  flattenᵐ (x ∷ xs) ys zs ws us = ap (x ∷_) (flattenᵐ xs ys zs ws us)

  bury : ∀ (xs ys zs ws : List X)
       → xs ++ ys ++ (zs ++ ws) ≡ (xs ++ (ys ++ zs)) ++ ws
  bury []       ys zs ws = sym (++-assoc ys zs ws)
  bury (x ∷ xs) ys zs ws = ap (x ∷_) (bury xs ys zs ws)

  -- (Add further named reassociations by the same five-step pattern:
  -- generic definition here, a PExp generator, a ⟦_⟧ᵖ clause, a refl clause
  -- in flatκ, and a soundκ leaf — sound-bury is the closest template.)

  -- ==========================================================================
  -- §1  Level 0: formal list expressions, and their two readings.
  -- ==========================================================================

  data LExp : Type o where
    [_]  : List X → LExp       -- opaque list atom
    _∷ᵉ_ : X → LExp → LExp     -- opaque element atom (pointed decompositions)
    _⊕_  : LExp → LExp → LExp
    εᵉ   : LExp

  infixr 24 _⊕_
  infixr 25 _∷ᵉ_

  private variable
    E E₁ E₂ E₃ F₁ F₂ : LExp

  -- The intended semantics: ⊕ is ++.
  ⟦_⟧ᵉ : LExp → List X
  ⟦ [ xs ] ⟧ᵉ  = xs
  ⟦ x ∷ᵉ E ⟧ᵉ  = x ∷ ⟦ E ⟧ᵉ
  ⟦ E₁ ⊕ E₂ ⟧ᵉ = ⟦ E₁ ⟧ᵉ ++ ⟦ E₂ ⟧ᵉ
  ⟦ εᵉ ⟧ᵉ      = []

  -- The Cayley/difference-list reading: an accumulator makes every pure
  -- reassociation of ⊕ hold definitionally, even on open expressions:
  --   eval ((E₁ ⊕ E₂) ⊕ E₃) κ ≐ eval (E₁ ⊕ (E₂ ⊕ E₃)) κ
  --   eval (E ⊕ εᵉ) κ ≐ eval E κ ≐ eval (εᵉ ⊕ E) κ
  eval : LExp → List X → List X
  eval [ xs ]    κ = xs ++ κ
  eval (x ∷ᵉ E)  κ = x ∷ eval E κ
  eval (E₁ ⊕ E₂) κ = eval E₁ (eval E₂ κ)
  eval εᵉ        κ = κ

  nf : LExp → List X
  nf E = eval E []

  -- The two readings agree (cons-by-cons; generalise the continuation).
  normκ : ∀ (E : LExp) (κ : List X) → ⟦ E ⟧ᵉ ++ κ ≡ eval E κ
  normκ [ xs ] κ = refl
  normκ (x ∷ᵉ E) κ = ap (x ∷_) (normκ E κ)
  normκ (E₁ ⊕ E) κ =
    ⟦ E₁ ⊕ E ⟧ᵉ ++ κ
      ≡⟨⟩
    (⟦ E₁ ⟧ᵉ ++ ⟦ E ⟧ᵉ) ++ κ
      ≡⟨ ++-assoc ⟦ E₁ ⟧ᵉ ⟦ E ⟧ᵉ κ ⟩
    ⟦ E₁ ⟧ᵉ ++ (⟦ E ⟧ᵉ ++ κ)
      ≡⟨ ap (⟦ E₁ ⟧ᵉ ++_ ) (normκ E κ) ⟩
    ⟦ E₁ ⟧ᵉ ++ (eval E κ)
      ≡⟨ normκ E₁ (eval E κ) ⟩
    eval E₁ (eval E κ)
      ≡⟨⟩
    eval (E₁ ⊕ E) κ
      ∎
  normκ εᵉ κ = refl

  norm₀ : ∀ (E : LExp) → ⟦ E ⟧ᵉ ≡ nf E
  norm₀ E = sym (++-idr ⟦ E ⟧ᵉ) ∙ normκ E []

  -- ==========================================================================
  -- §2  Level 1: formal structural paths.
  -- ==========================================================================

  data PExp : LExp → LExp → Type o where
    -- groupoid structure
    idᵖ  : PExp E E
    _∙ᵖ_ : PExp E₁ E₂ → PExp E₂ E₃ → PExp E₁ E₃
    symᵖ : PExp E₁ E₂ → PExp E₂ E₁
    -- congruence: ap (x ∷_), and the one-sided whiskers ap (– ++_) / ap (_++ –)
    consᵖ : (x : X) → PExp E₁ E₂ → PExp (x ∷ᵉ E₁) (x ∷ᵉ E₂)
    _◁ᵖ_  : (E : LExp) → PExp F₁ F₂ → PExp (E ⊕ F₁) (E ⊕ F₂)
    _▷ᵖ_  : PExp E₁ E₂ → (E : LExp) → PExp (E₁ ⊕ E) (E₂ ⊕ E)
    -- base generators
    assocᵖ : (E₁ E₂ E₃ : LExp) → PExp ((E₁ ⊕ E₂) ⊕ E₃) (E₁ ⊕ (E₂ ⊕ E₃))
    idrᵖ   : (E : LExp) → PExp (E ⊕ εᵉ) E
    -- named composite reassociations, one generator each.  These take LExp
    -- arguments (not list atoms) so that quoted goals mixing granularities —
    -- e.g. flattenʳ (xs ++ ys) … next to a segment about xs and ys — still
    -- meet at judgmentally equal endpoint expressions.
    flattenˡᵖ : ∀ (E₁ E₂ E₃ E₄ : LExp)
              → PExp ((E₁ ⊕ E₂ ⊕ E₃) ⊕ E₄) (E₁ ⊕ E₂ ⊕ (E₃ ⊕ E₄))
    flattenʳᵖ : ∀ (E₁ E₂ E₃ E₄ : LExp)
              → PExp (E₁ ⊕ (E₂ ⊕ E₃ ⊕ E₄)) ((E₁ ⊕ E₂) ⊕ E₃ ⊕ E₄)
    flattenᵐᵖ : ∀ (E₁ E₂ E₃ E₄ E₅ : LExp)
              → PExp (E₁ ⊕ ((E₂ ⊕ E₃ ⊕ E₄) ⊕ E₅))
                     ((E₁ ⊕ E₂) ⊕ E₃ ⊕ (E₄ ⊕ E₅))
    buryᵖ : ∀ (E₁ E₂ E₃ E₄ : LExp)
          → PExp (E₁ ⊕ E₂ ⊕ (E₃ ⊕ E₄)) ((E₁ ⊕ (E₂ ⊕ E₃)) ⊕ E₄)

  infixr 30 _∙ᵖ_
  infix 34 _◁ᵖ_
  infix 34 _▷ᵖ_

  -- Interpretation.  Every clause is DEFINITIONALLY the path a client
  -- writes, so `solve P Q h` typechecks against goals verbatim.
  ⟦_⟧ᵖ : PExp E₁ E₂ → ⟦ E₁ ⟧ᵉ ≡ ⟦ E₂ ⟧ᵉ
  ⟦ idᵖ ⟧ᵖ                 = refl
  ⟦ P ∙ᵖ Q ⟧ᵖ              = ⟦ P ⟧ᵖ ∙ ⟦ Q ⟧ᵖ
  ⟦ symᵖ P ⟧ᵖ              = sym ⟦ P ⟧ᵖ
  ⟦ consᵖ x P ⟧ᵖ           = ap (x ∷_) ⟦ P ⟧ᵖ
  ⟦ E ◁ᵖ P ⟧ᵖ              = ap (⟦ E ⟧ᵉ ++_) ⟦ P ⟧ᵖ
  ⟦ P ▷ᵖ E ⟧ᵖ              = ap (_++ ⟦ E ⟧ᵉ) ⟦ P ⟧ᵖ
  ⟦ assocᵖ E₁ E₂ E₃ ⟧ᵖ     = ++-assoc ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ
  ⟦ idrᵖ E ⟧ᵖ              = ++-idr ⟦ E ⟧ᵉ
  ⟦ flattenˡᵖ E₁ E₂ E₃ E₄ ⟧ᵖ    = flattenˡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ
  ⟦ flattenʳᵖ E₁ E₂ E₃ E₄ ⟧ᵖ    = flattenʳ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ
  ⟦ flattenᵐᵖ E₁ E₂ E₃ E₄ E₅ ⟧ᵖ = flattenᵐ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ
  ⟦ buryᵖ E₁ E₂ E₃ E₄ ⟧ᵖ        = bury ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ

  -- ==========================================================================
  -- §3  The nf-level residue.  Thanks to eval's accumulator, every pure
  -- reassociation generator leaves residue refl — DEFINITIONALLY.  Only ∙ᵖ
  -- builds a composite (an hcomp; path composition never computes in cubical
  -- Agda), which is why solve carries the `flat P ≡ flat Q` premise: at
  -- concrete call sites it is a composite-of-refls equation, closed by refl
  -- or ∙-idl/∙-idr (see tests).  Note the ▷ᵖ clause: the whisker moves into
  -- the continuation, no ap needed.
  -- ==========================================================================

  flatκ : PExp E₁ E₂ → ∀ (κ : List X) → eval E₁ κ ≡ eval E₂ κ
  flatκ idᵖ         κ = refl
  flatκ (P ∙ᵖ Q)    κ = flatκ P κ ∙ flatκ Q κ
  flatκ (symᵖ P)    κ = sym (flatκ P κ)
  flatκ (consᵖ x P) κ = ap (x ∷_) (flatκ P κ)
  flatκ (E ◁ᵖ P)    κ = ap (eval E) (flatκ P κ)
  flatκ (P ▷ᵖ E)    κ = flatκ P (eval E κ)
  flatκ (assocᵖ E₁ E₂ E₃) κ = refl
  flatκ (idrᵖ E)    κ = refl
  flatκ (flattenˡᵖ E₁ E₂ E₃ E₄) κ = refl
  flatκ (flattenʳᵖ E₁ E₂ E₃ E₄) κ = refl
  flatκ (flattenᵐᵖ E₁ E₂ E₃ E₄ E₅) κ = refl
  flatκ (buryᵖ E₁ E₂ E₃ E₄) κ = refl

  flat : PExp E₁ E₂ → nf E₁ ≡ nf E₂
  flat P = flatκ P []

  -- ==========================================================================
  -- §4  Soundness: ⟦P⟧ᵖ fits in a square over its residue, with the
  -- normalisation paths as vertical sides (the analogue of Cat.Bi.Solver's
  -- eval₂-sound).
  --
  --                 ap (_++ κ) ⟦P⟧ᵖ
  --      ⟦E₁⟧ᵉ ++ κ ---------------- ⟦E₂⟧ᵉ ++ κ
  --          |                            |
  --  normκ E₁ κ                      normκ E₂ κ
  --          |                            |
  --      eval E₁ κ ----------------- eval E₂ κ
  --                    flatκ P κ
  --
  -- The structural cases are mechanical: (i) the SIDES of each square are
  -- normκ's equational chains, so the ◁ᵖ/▷ᵖ cases are that same chain re-run
  -- at interval i — vertical pasting of squares is pointwise ∙, and
  -- mirroring the chain step-for-step makes the side endpoints judgmental
  -- whatever the reasoning syntax desugars to; (ii) horizontal pasting is
  -- 1lab's _∙₂_, with the top edge fixed along ap-∙; (iii) the congruence
  -- cases are the IH under the constructor.  The LEAF lemmas are the seed
  -- coherences (triangle, pentagon, and the named-reassociation bridges).
  -- ==========================================================================

  private
    -- Reindex a square along an equality of its top edge.
    sq-cast
      : {a₀ a₁ c₀ c₁ : List X} {t t' : a₀ ≡ a₁} {b : c₀ ≡ c₁}
        {l : a₀ ≡ c₀} {r : a₁ ≡ c₁}
      → t ≡ t'
      → PathP (λ i → t i ≡ b i) l r → PathP (λ i → t' i ≡ b i) l r
    sq-cast {b = b} {l = l} {r = r} et =
      subst (λ t → PathP (λ i → t i ≡ b i) l r) et

    -- Reindex both edges.
    sq-cast₂
      : {a₀ a₁ c₀ c₁ : List X} {t t' : a₀ ≡ a₁} {b b' : c₀ ≡ c₁}
        {l : a₀ ≡ c₀} {r : a₁ ≡ c₁}
      → t ≡ t' → b ≡ b'
      → PathP (λ i → t i ≡ b i) l r → PathP (λ i → t' i ≡ b' i) l r
    sq-cast₂ {l = l} {r = r} et eb =
      transport (λ j → PathP (λ i → et j i ≡ eb j i) l r)

    -- A bottom-refl square from its homogeneous form.
    ∙→sq : {xs ys zs : List X} {T : xs ≡ ys} {L : xs ≡ zs} {R : ys ≡ zs}
         → L ≡ T ∙ R → PathP (λ i → T i ≡ zs) L R
    ∙→sq {T = T} {R = R} h =
      h ◁ ((λ i → (λ j → T (i ∨ j)) ∙ R) ▷ ∙-idl R)

    -- Naturality of ++-assoc in its last argument (J is harmless here:
    -- nothing ever computes through these 2-cells).
    assoc-natʳ
      : ∀ (xs ys : List X) {ws ws' : List X} (q : ws ≡ ws')
      → ap ((xs ++ ys) ++_) q ∙ ++-assoc xs ys ws'
      ≡ ++-assoc xs ys ws ∙ ap (xs ++_) (ap (ys ++_) q)
    assoc-natʳ xs ys {ws} =
      J (λ ws' q → ap ((xs ++ ys) ++_) q ∙ ++-assoc xs ys ws'
                 ≡ ++-assoc xs ys ws ∙ ap (xs ++_) (ap (ys ++_) q))
        (∙-idl _ ∙ sym (∙-idr _))

    -- The Mac Lane pentagon for ++, in the exact bracketing sound-assoc
    -- consumes.  Cons-by-cons; the base case is pure unit algebra.
    penta
      : ∀ (xs ys zs κ : List X)
      → ++-assoc (xs ++ ys) zs κ ∙ ++-assoc xs ys (zs ++ κ)
      ≡ ap (_++ κ) (++-assoc xs ys zs)
        ∙ (++-assoc xs (ys ++ zs) κ ∙ ap (xs ++_) (++-assoc ys zs κ))
    penta [] ys zs κ = ∙-idr _ ∙ sym (∙-idl _ ∙ ∙-idl _)
    penta (x ∷ xs) ys zs κ =
        sym (ap-∙ (x ∷_) (++-assoc (xs ++ ys) zs κ) (++-assoc xs ys (zs ++ κ)))
      ∙ ap (ap (x ∷_)) (penta xs ys zs κ)
      ∙ ap-∙ (x ∷_) (ap (_++ κ) (++-assoc xs ys zs))
          (++-assoc xs (ys ++ zs) κ ∙ ap (xs ++_) (++-assoc ys zs κ))
      ∙ ap (ap (x ∷_) (ap (_++ κ) (++-assoc xs ys zs)) ∙_)
          (ap-∙ (x ∷_) (++-assoc xs (ys ++ zs) κ) (ap (xs ++_) (++-assoc ys zs κ)))

  -- ---- leaf obligations: the actual mathematical content -------------------

  -- ++-assoc against the two normκ routes: the pentagon, in seed form.
  sound-assoc
    : ∀ (E₁ E₂ E₃ : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (++-assoc ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ) i
                 ≡ eval E₁ (eval E₂ (eval E₃ κ)))
        (normκ ((E₁ ⊕ E₂) ⊕ E₃) κ) (normκ (E₁ ⊕ (E₂ ⊕ E₃)) κ)
  sound-assoc E₁ E₂ E₃ κ = ∙→sq eq where
    xs = ⟦ E₁ ⟧ᵉ
    ys = ⟦ E₂ ⟧ᵉ
    zs = ⟦ E₃ ⟧ᵉ
    e₃ = eval E₃ κ
    s₁ = ++-assoc (xs ++ ys) zs κ
    s₂ = ap ((xs ++ ys) ++_) (normκ E₃ κ)
    x₁ = ++-assoc xs ys e₃
    x₂ = ap (xs ++_) (normκ E₂ e₃)
    x₃ = normκ E₁ (eval E₂ e₃)
    u₁ = ++-assoc xs ys (zs ++ κ)
    u₂ = ap (xs ++_) (ap (ys ++_) (normκ E₃ κ))
    T = ap (_++ κ) (++-assoc xs ys zs)
    t₁ = ++-assoc xs (ys ++ zs) κ
    t₂ = ap (xs ++_) (++-assoc ys zs κ)

    -- ap (xs ++_) distributed over normκ (E₂ ⊕ E₃) κ's chain.
    apN-split
      : ap (xs ++_) (normκ (E₂ ⊕ E₃) κ)
      ≡ t₂ ∙ (u₂ ∙ (x₂ ∙ refl))
    apN-split =
        ap-∙ (xs ++_) (++-assoc ys zs κ)
          (ap (ys ++_) (normκ E₃ κ) ∙ (normκ E₂ e₃ ∙ refl))
      ∙ ap (t₂ ∙_)
          (ap-∙ (xs ++_) (ap (ys ++_) (normκ E₃ κ)) (normκ E₂ e₃ ∙ refl))
      ∙ ap (λ z → t₂ ∙ (u₂ ∙ z)) (ap-∙ (xs ++_) (normκ E₂ e₃) refl)

    tail-fold
      : t₂ ∙ (u₂ ∙ (x₂ ∙ x₃))
      ≡ ap (xs ++_) (normκ (E₂ ⊕ E₃) κ) ∙ (x₃ ∙ refl)
    tail-fold =
        ap (t₂ ∙_) (∙-assoc u₂ x₂ x₃)
      ∙ ∙-assoc t₂ (u₂ ∙ x₂) x₃
      ∙ ap₂ _∙_ (ap (λ z → t₂ ∙ (u₂ ∙ z)) (sym (∙-idr x₂))) (sym (∙-idr x₃))
      ∙ ap (_∙ (x₃ ∙ refl)) (sym apN-split)

    eq : normκ ((E₁ ⊕ E₂) ⊕ E₃) κ ≡ T ∙ normκ (E₁ ⊕ (E₂ ⊕ E₃)) κ
    eq =
      normκ ((E₁ ⊕ E₂) ⊕ E₃) κ
        ≡⟨⟩
      s₁ ∙ (s₂ ∙ (normκ (E₁ ⊕ E₂) e₃ ∙ refl))
        ≡⟨ ap (λ z → s₁ ∙ (s₂ ∙ z)) (∙-idr (normκ (E₁ ⊕ E₂) e₃)) ⟩
      s₁ ∙ (s₂ ∙ (x₁ ∙ (x₂ ∙ (x₃ ∙ refl))))
        ≡⟨ ap (λ z → s₁ ∙ (s₂ ∙ (x₁ ∙ (x₂ ∙ z)))) (∙-idr x₃) ⟩
      s₁ ∙ (s₂ ∙ (x₁ ∙ (x₂ ∙ x₃)))
        ≡⟨ ap (s₁ ∙_) (∙-assoc s₂ x₁ (x₂ ∙ x₃)) ⟩
      s₁ ∙ ((s₂ ∙ x₁) ∙ (x₂ ∙ x₃))
        ≡⟨ ap (λ z → s₁ ∙ (z ∙ (x₂ ∙ x₃))) (assoc-natʳ xs ys (normκ E₃ κ)) ⟩
      s₁ ∙ ((u₁ ∙ u₂) ∙ (x₂ ∙ x₃))
        ≡⟨ ap (s₁ ∙_) (sym (∙-assoc u₁ u₂ (x₂ ∙ x₃))) ⟩
      s₁ ∙ (u₁ ∙ (u₂ ∙ (x₂ ∙ x₃)))
        ≡⟨ ∙-assoc s₁ u₁ (u₂ ∙ (x₂ ∙ x₃)) ⟩
      (s₁ ∙ u₁) ∙ (u₂ ∙ (x₂ ∙ x₃))
        ≡⟨ ap (_∙ (u₂ ∙ (x₂ ∙ x₃))) (penta xs ys zs κ) ⟩
      (T ∙ (t₁ ∙ t₂)) ∙ (u₂ ∙ (x₂ ∙ x₃))
        ≡⟨ sym (∙-assoc T (t₁ ∙ t₂) (u₂ ∙ (x₂ ∙ x₃))) ⟩
      T ∙ ((t₁ ∙ t₂) ∙ (u₂ ∙ (x₂ ∙ x₃)))
        ≡⟨ ap (T ∙_) (sym (∙-assoc t₁ t₂ (u₂ ∙ (x₂ ∙ x₃)))) ⟩
      T ∙ (t₁ ∙ (t₂ ∙ (u₂ ∙ (x₂ ∙ x₃))))
        ≡⟨ ap (λ z → T ∙ (t₁ ∙ z)) tail-fold ⟩
      T ∙ (t₁ ∙ (ap (xs ++_) (normκ (E₂ ⊕ E₃) κ) ∙ (x₃ ∙ refl)))
        ≡⟨⟩
      T ∙ normκ (E₁ ⊕ (E₂ ⊕ E₃)) κ
        ∎

  -- ++-idr against normκ: the triangle.  The leaf recipe:
  --   1. reasoning chains desugar to right-nested ∙ with a trailing refl
  --      (only ≡⟨⟩-syntax has a syntax declaration; nothing fuses to ∙∙);
  --   2. isolate the pure core (tri: the only i-varying segment) and prove it
  --      cons-by-cons — both ++-idr and ++-assoc peel cons definitionally;
  --   3. mirror the normκ chain at interval i, substituting the core for the
  --      segment that varies — at i = 0 this IS normκ (E ⊕ εᵉ) κ verbatim;
  --   4. at i = 1 the mirror degenerates to a composite of refls around
  --      normκ E κ; discharge it with unit laws under _▷_.
  private
    tri : ∀ (xs κ : List X)
        → PathP (λ i → ++-idr xs i ++ κ ≡ xs ++ κ) (++-assoc xs [] κ) refl
    tri []       κ = refl
    tri (x ∷ xs) κ i j = x ∷ tri xs κ i j

  sound-idr
    : ∀ (E : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (++-idr ⟦ E ⟧ᵉ) i ≡ eval E κ)
        (normκ (E ⊕ εᵉ) κ) (normκ E κ)
  sound-idr E κ =
    (λ i → tri ⟦ E ⟧ᵉ κ i
         ∙ ap (⟦ E ⟧ᵉ ++_) (normκ εᵉ κ)
         ∙ normκ E (eval εᵉ κ)
         ∙ refl)
    ▷ (∙-idl _ ∙ ∙-idl _ ∙ ∙-idr _)

  -- Named reassociations, each via a bridge to a core composite (a small
  -- ap-∙ induction) and an assembly from sound-assoc and the pasting
  -- combinators (not by calling soundκ on the composite — the termination
  -- checker cannot see it as smaller).
  flattenˡ≡
    : ∀ (xs ys zs ws : List X)
    → flattenˡ xs ys zs ws
    ≡ ++-assoc xs (ys ++ zs) ws ∙ ap (xs ++_) (++-assoc ys zs ws)
  flattenˡ≡ []       ys zs ws = sym (∙-idl _)
  flattenˡ≡ (x ∷ xs) ys zs ws =
      ap (ap (x ∷_)) (flattenˡ≡ xs ys zs ws)
    ∙ ap-∙ (x ∷_) (++-assoc xs (ys ++ zs) ws) (ap (xs ++_) (++-assoc ys zs ws))

  sound-flattenˡ
    : ∀ (E₁ E₂ E₃ E₄ : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (flattenˡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ) i
                 ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ κ))))
        (normκ ((E₁ ⊕ E₂ ⊕ E₃) ⊕ E₄) κ)
        (normκ (E₁ ⊕ E₂ ⊕ (E₃ ⊕ E₄)) κ)
  sound-flattenˡ E₁ E₂ E₃ E₄ κ =
    sq-cast₂ et (∙-idl refl)
      (sound-assoc E₁ (E₂ ⊕ E₃) E₄ κ ∙₂ whisk)
    where
      whisk
        : PathP (λ i → ap (_++ κ)
                          (ap (⟦ E₁ ⟧ᵉ ++_) (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ)) i
                     ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ κ))))
            (normκ (E₁ ⊕ ((E₂ ⊕ E₃) ⊕ E₄)) κ)
            (normκ (E₁ ⊕ (E₂ ⊕ (E₃ ⊕ E₄))) κ)
      whisk i =
          ++-assoc ⟦ E₁ ⟧ᵉ (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ i) κ
        ∙ ap (⟦ E₁ ⟧ᵉ ++_) (sound-assoc E₂ E₃ E₄ κ i)
        ∙ normκ E₁ (eval E₂ (eval E₃ (eval E₄ κ)))
        ∙ refl
      et =
          sym (ap-∙ (_++ κ) (++-assoc ⟦ E₁ ⟧ᵉ (⟦ E₂ ⟧ᵉ ++ ⟦ E₃ ⟧ᵉ) ⟦ E₄ ⟧ᵉ)
                (ap (⟦ E₁ ⟧ᵉ ++_) (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ)))
        ∙ ap (ap (_++ κ)) (sym (flattenˡ≡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ))

  sound-flattenʳ
    : ∀ (E₁ E₂ E₃ E₄ : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (flattenʳ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ) i
                 ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ κ))))
        (normκ (E₁ ⊕ (E₂ ⊕ E₃ ⊕ E₄)) κ)
        (normκ ((E₁ ⊕ E₂) ⊕ E₃ ⊕ E₄) κ)
  sound-flattenʳ E₁ E₂ E₃ E₄ κ =
    sq-cast (ap (ap (_++ κ)) (sym (flattenʳ≡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ)))
      (λ i → sound-assoc E₁ E₂ (E₃ ⊕ E₄) κ (~ i))
    where
      flattenʳ≡
        : ∀ (xs ys zs ws : List X)
        → flattenʳ xs ys zs ws ≡ sym (++-assoc xs ys (zs ++ ws))
      flattenʳ≡ []       ys zs ws = refl
      flattenʳ≡ (x ∷ xs) ys zs ws = ap (ap (x ∷_)) (flattenʳ≡ xs ys zs ws)

  sound-flattenᵐ
    : ∀ (E₁ E₂ E₃ E₄ E₅ : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (flattenᵐ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ) i
                 ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ (eval E₅ κ)))))
        (normκ (E₁ ⊕ ((E₂ ⊕ E₃ ⊕ E₄) ⊕ E₅)) κ)
        (normκ ((E₁ ⊕ E₂) ⊕ E₃ ⊕ (E₄ ⊕ E₅)) κ)
  sound-flattenᵐ E₁ E₂ E₃ E₄ E₅ κ =
    sq-cast₂ et (∙-idl refl)
      (whisk ∙₂ (λ i → sound-assoc E₁ E₂ (E₃ ⊕ (E₄ ⊕ E₅)) κ (~ i)))
    where
      flattenᵐ≡
        : ∀ (xs ys zs ws us : List X)
        → flattenᵐ xs ys zs ws us
        ≡ ap (xs ++_) (flattenˡ ys zs ws us) ∙ sym (++-assoc xs ys (zs ++ ws ++ us))
      flattenᵐ≡ []       ys zs ws us = sym (∙-idr _)
      flattenᵐ≡ (x ∷ xs) ys zs ws us =
          ap (ap (x ∷_)) (flattenᵐ≡ xs ys zs ws us)
        ∙ ap-∙ (x ∷_) (ap (xs ++_) (flattenˡ ys zs ws us))
            (sym (++-assoc xs ys (zs ++ ws ++ us)))

      whisk
        : PathP (λ i → ap (_++ κ)
                          (ap (⟦ E₁ ⟧ᵉ ++_) (flattenˡ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ)) i
                     ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ (eval E₅ κ)))))
            (normκ (E₁ ⊕ ((E₂ ⊕ E₃ ⊕ E₄) ⊕ E₅)) κ)
            (normκ (E₁ ⊕ (E₂ ⊕ (E₃ ⊕ (E₄ ⊕ E₅)))) κ)
      whisk i =
          ++-assoc ⟦ E₁ ⟧ᵉ (flattenˡ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ i) κ
        ∙ ap (⟦ E₁ ⟧ᵉ ++_) (sound-flattenˡ E₂ E₃ E₄ E₅ κ i)
        ∙ normκ E₁ (eval E₂ (eval E₃ (eval E₄ (eval E₅ κ))))
        ∙ refl
      et =
          sym (ap-∙ (_++ κ) (ap (⟦ E₁ ⟧ᵉ ++_) (flattenˡ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ))
                (sym (++-assoc ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ (⟦ E₃ ⟧ᵉ ++ ⟦ E₄ ⟧ᵉ ++ ⟦ E₅ ⟧ᵉ))))
        ∙ ap (ap (_++ κ)) (sym (flattenᵐ≡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ ⟦ E₅ ⟧ᵉ))

  sound-bury
    : ∀ (E₁ E₂ E₃ E₄ : LExp) (κ : List X)
    → PathP (λ i → ap (_++ κ) (bury ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ) i
                 ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ κ))))
        (normκ (E₁ ⊕ E₂ ⊕ (E₃ ⊕ E₄)) κ)
        (normκ ((E₁ ⊕ (E₂ ⊕ E₃)) ⊕ E₄) κ)
  sound-bury E₁ E₂ E₃ E₄ κ =
    sq-cast₂ et (∙-idl refl)
      (whisk ∙₂ (λ i → sound-assoc E₁ (E₂ ⊕ E₃) E₄ κ (~ i)))
    where
      bury≡
        : ∀ (xs ys zs ws : List X)
        → bury xs ys zs ws
        ≡ ap (xs ++_) (sym (++-assoc ys zs ws)) ∙ sym (++-assoc xs (ys ++ zs) ws)
      bury≡ []       ys zs ws = sym (∙-idr _)
      bury≡ (x ∷ xs) ys zs ws =
          ap (ap (x ∷_)) (bury≡ xs ys zs ws)
        ∙ ap-∙ (x ∷_) (ap (xs ++_) (sym (++-assoc ys zs ws)))
            (sym (++-assoc xs (ys ++ zs) ws))

      whisk
        : PathP (λ i → ap (_++ κ)
                          (ap (⟦ E₁ ⟧ᵉ ++_) (sym (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ))) i
                     ≡ eval E₁ (eval E₂ (eval E₃ (eval E₄ κ))))
            (normκ (E₁ ⊕ (E₂ ⊕ (E₃ ⊕ E₄))) κ)
            (normκ (E₁ ⊕ ((E₂ ⊕ E₃) ⊕ E₄)) κ)
      whisk i =
          ++-assoc ⟦ E₁ ⟧ᵉ (sym (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ) i) κ
        ∙ ap (⟦ E₁ ⟧ᵉ ++_) (sound-assoc E₂ E₃ E₄ κ (~ i))
        ∙ normκ E₁ (eval E₂ (eval E₃ (eval E₄ κ)))
        ∙ refl
      et =
          sym (ap-∙ (_++ κ) (ap (⟦ E₁ ⟧ᵉ ++_) (sym (++-assoc ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ)))
                (sym (++-assoc ⟦ E₁ ⟧ᵉ (⟦ E₂ ⟧ᵉ ++ ⟦ E₃ ⟧ᵉ) ⟦ E₄ ⟧ᵉ)))
        ∙ ap (ap (_++ κ)) (sym (bury≡ ⟦ E₁ ⟧ᵉ ⟦ E₂ ⟧ᵉ ⟦ E₃ ⟧ᵉ ⟦ E₄ ⟧ᵉ))

  -- ---- the induction ------------------------------------------------------

  soundκ : (P : PExp E₁ E₂) (κ : List X)
         → PathP (λ i → ap (_++ κ) ⟦ P ⟧ᵖ i ≡ flatκ P κ i)
             (normκ E₁ κ) (normκ E₂ κ)
  soundκ idᵖ κ = refl
  soundκ (P ∙ᵖ Q) κ =
    sq-cast (sym (ap-∙ (_++ κ) ⟦ P ⟧ᵖ ⟦ Q ⟧ᵖ)) (soundκ P κ ∙₂ soundκ Q κ)
  soundκ (symᵖ P) κ i = soundκ P κ (~ i)
  soundκ (consᵖ x P) κ i j = x ∷ soundκ P κ i j
  soundκ (E ◁ᵖ P) κ i =
    (⟦ E ⟧ᵉ ++ ⟦ P ⟧ᵖ i) ++ κ
      ≡⟨ ++-assoc ⟦ E ⟧ᵉ (⟦ P ⟧ᵖ i) κ ⟩
    ⟦ E ⟧ᵉ ++ (⟦ P ⟧ᵖ i ++ κ)
      ≡⟨ ap (⟦ E ⟧ᵉ ++_ ) (soundκ P κ i) ⟩
    ⟦ E ⟧ᵉ ++ (flatκ P κ i)
      ≡⟨ normκ E (flatκ P κ i) ⟩
    eval E (flatκ P κ i)
      ∎
  soundκ (P ▷ᵖ E) κ i =
    (⟦ P ⟧ᵖ i ++ ⟦ E ⟧ᵉ) ++ κ
      ≡⟨ ++-assoc (⟦ P ⟧ᵖ i) ⟦ E ⟧ᵉ κ ⟩
    ⟦ P ⟧ᵖ i ++ (⟦ E ⟧ᵉ ++ κ)
      ≡⟨ ap (⟦ P ⟧ᵖ i ++_ ) (normκ E κ) ⟩
    ⟦ P ⟧ᵖ i ++ eval E κ
      ≡⟨ soundκ P (eval E κ) i ⟩
    flatκ P (eval E κ) i
      ∎
  soundκ (assocᵖ E₁ E₂ E₃) κ = sound-assoc E₁ E₂ E₃ κ
  soundκ (idrᵖ E) κ = sound-idr E κ
  soundκ (flattenˡᵖ E₁' E₂' E₃' E₄') κ = sound-flattenˡ E₁' E₂' E₃' E₄' κ
  soundκ (flattenʳᵖ E₁' E₂' E₃' E₄') κ = sound-flattenʳ E₁' E₂' E₃' E₄' κ
  soundκ (flattenᵐᵖ E₁' E₂' E₃' E₄' E₅') κ = sound-flattenᵐ E₁' E₂' E₃' E₄' E₅' κ
  soundκ (buryᵖ E₁' E₂' E₃' E₄') κ = sound-bury E₁' E₂' E₃' E₄' κ

  -- Closed form at κ = []: mirror norm₀'s definition at interval i.
  sound : (P : PExp E₁ E₂)
        → PathP (λ i → ⟦ P ⟧ᵖ i ≡ flat P i) (norm₀ E₁) (norm₀ E₂)
  sound P i = sym (++-idr (⟦ P ⟧ᵖ i)) ∙ soundκ P [] i

  -- ==========================================================================
  -- §5  The solver.  Two codes with identified residues denote equal paths:
  -- both sound-squares share their vertical sides, so rebasing one bottom
  -- along h, pasting, and cancelling the sides gives top ≡ top.
  -- ==========================================================================

  abstract
    solve : (P Q : PExp E₁ E₂) → flat P ≡ flat Q → ⟦ P ⟧ᵖ ≡ ⟦ Q ⟧ᵖ
    solve {E₁} {E₂} P Q h j i = K i j
      where
        -- sound Q, rebased over flat P along h.
        SQ' : PathP (λ i → ⟦ Q ⟧ᵖ i ≡ flat P i) (norm₀ E₁) (norm₀ E₂)
        SQ' = transport
          (λ j → PathP (λ i → ⟦ Q ⟧ᵖ i ≡ h (~ j) i) (norm₀ E₁) (norm₀ E₂))
          (sound Q)

        -- Paste sound P with the vertical flip of SQ' (pointwise ∙), then
        -- cancel the shared sides.
        K0 : PathP (λ i → ⟦ P ⟧ᵖ i ≡ ⟦ Q ⟧ᵖ i)
               (norm₀ E₁ ∙ sym (norm₀ E₁)) (norm₀ E₂ ∙ sym (norm₀ E₂))
        K0 i = sound P i ∙ (λ j → SQ' i (~ j))

        K : PathP (λ i → ⟦ P ⟧ᵖ i ≡ ⟦ Q ⟧ᵖ i) refl refl
        K = sym (∙-invr (norm₀ E₁)) ◁ K0 ▷ ∙-invr (norm₀ E₂)

  -- PathP base-swapping: a PathP over one route is a PathP over any
  -- solver-equal route.  All one ever needs when the family's fibres are
  -- sets (any two transfers agree).
  over : ∀ {ℓ} (F : List X → Type ℓ) (P Q : PExp E₁ E₂) → flat P ≡ flat Q
       → {x : F ⟦ E₁ ⟧ᵉ} {y : F ⟦ E₂ ⟧ᵉ}
       → PathP (λ i → F (⟦ P ⟧ᵖ i)) x y → PathP (λ i → F (⟦ Q ⟧ᵖ i)) x y
  over F P Q h {x} {y} = subst (λ p → PathP (λ i → F (p i)) x y) (solve P Q h)

  -- ==========================================================================
  -- §6  The cast calculus (Tier 1.5).  Formal cast towers over an arbitrary
  -- family F: an opaque atom under nested substs along codes.  `reduce`
  -- fuses the tower into a single subst along the composite code (only
  -- subst-∙ functoriality — nothing about F); `solve-cast` then decides
  -- equality of two fused towers over the SAME atom via the solver.  The
  -- normal call shape is
  --   reduce c₁ ∙ solve-cast t code₁ code₂ premise ∙ sym (reduce c₂)
  -- (see test-cast-cancel below for the ++ []-cancellation example).
  -- ==========================================================================

  module Cast {ℓ} (F : List X → Type ℓ) where

    data CExp : LExp → Type (o ⊔ ℓ) where
      ⟪_⟫   : F ⟦ E ⟧ᵉ → CExp E
      castᵖ : PExp E₁ E₂ → CExp E₁ → CExp E₂

    ⟦_⟧ᶜ : CExp E → F ⟦ E ⟧ᵉ
    ⟦ ⟪ t ⟫ ⟧ᶜ     = t
    ⟦ castᵖ P c ⟧ᶜ = subst F ⟦ P ⟧ᵖ ⟦ c ⟧ᶜ

    -- Fusion normal form: one cast of the atom along a composite code.
    record Fused (E : LExp) : Type (o ⊔ ℓ) where
      constructor fused
      field
        {src} : LExp
        atom  : F ⟦ src ⟧ᵉ
        code  : PExp src E
    open Fused

    fuse : CExp E → Fused E
    fuse ⟪ t ⟫       = fused t idᵖ
    fuse (castᵖ P c) = fused (fuse c .atom) (fuse c .code ∙ᵖ P)

    -- Fusion is sound: only subst-∙, generic in F.
    reduce : (c : CExp E) → ⟦ c ⟧ᶜ ≡ subst F ⟦ fuse c .code ⟧ᵖ (fuse c .atom)
    reduce ⟪ t ⟫       = sym (transport-refl t)
    reduce (castᵖ P c) =
        ap (subst F ⟦ P ⟧ᵖ) (reduce c)
      ∙ sym (subst-∙ F ⟦ fuse c .code ⟧ᵖ ⟦ P ⟧ᵖ (fuse c .atom))

    -- Two casts of the same atom along solver-equal codes agree.
    solve-cast
      : {E₀ : LExp} (t : F ⟦ E₀ ⟧ᵉ) (P Q : PExp E₀ E)
      → flat P ≡ flat Q
      → subst F ⟦ P ⟧ᵖ t ≡ subst F ⟦ Q ⟧ᵖ t
    solve-cast t P Q h = ap (λ p → subst F p t) (solve P Q h)

-- ============================================================================
-- Tier B: the reflection layer.  Quotes both sides of a `p ≡ q` goal into
-- PExp codes and synthesises the residue premise, in one pass.
--
-- Premise synthesis is type-directed: alongside each code the quoter builds
-- a proof that the code's residue is refl, as an application of the
-- collapse-* combinators below.  Each combinator is stated over loops
-- p : x ≡ x — exactly the form residues take at concrete call sites — so
-- elaboration solves every implicit from the expected type, first-order; no
-- meta is ever blocked under an interval application, and no term under a
-- binder is ever extracted (element positions under lambdas are emitted as
-- `unknown` and recovered by unification, a Miller pattern).
-- ============================================================================

collapse-eq : ∀ {ℓ} {A : Type ℓ} {x : A} {p q : x ≡ x}
            → p ≡ refl → q ≡ refl → p ≡ q
collapse-eq cp cq = cp ∙ sym cq

collapse-∙ : ∀ {ℓ} {A : Type ℓ} {x : A} {p q : x ≡ x}
           → p ≡ refl → q ≡ refl → p ∙ q ≡ refl
collapse-∙ cp cq = ap₂ _∙_ cp cq ∙ ∙-idl refl

collapse-ap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x : A}
              {p : x ≡ x} → p ≡ refl → ap f p ≡ refl
collapse-ap f cp = ap (ap f) cp

collapse-sym : ∀ {ℓ} {A : Type ℓ} {x : A} {p : x ≡ x}
             → p ≡ refl → sym p ≡ refl
collapse-sym cp = ap sym cp

module Reflection where
  open import 1Lab.Reflection hiding (reverse)
  open import 1Lab.Reflection.Solver using (solver-failed)
  open import 1Lab.Reflection.Subst using (subst-tm ; singletonS)

  private
    -- Quote a list-valued Term into an LExp code.
    build-lexp : Term → Term
    build-lexp (con (quote List._∷_) (x v∷ xs v∷ [])) =
      con (quote NbE._∷ᵉ_) (x v∷ build-lexp xs v∷ [])
    build-lexp (def (quote _++_) (_ h∷ _ h∷ xs v∷ ys v∷ [])) =
      con (quote NbE._⊕_) (build-lexp xs v∷ build-lexp ys v∷ [])
    build-lexp (con (quote List.[]) _) = con (quote NbE.εᵉ) []
    build-lexp t = con (quote NbE.[_]) (t v∷ [])

  -- build-path tm ⇒ (code, loop-collapse proof for the code's residue).
  build-path : Term → TC (Term × Term)
  private
    build-ap : Term → Term → TC (Term × Term)

  build-path (def (quote refl) _) =
    pure (con (quote NbE.idᵖ) [] , “refl”)
  build-path (def (quote _∙_) (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ p v∷ q v∷ [])) = do
    (eP , cP) ← build-path p
    (eQ , cQ) ← build-path q
    pure ( con (quote NbE._∙ᵖ_) (eP v∷ eQ v∷ [])
         , def (quote collapse-∙) (cP v∷ cQ v∷ []) )
  build-path (def (quote sym) (_ h∷ _ h∷ _ h∷ _ h∷ p v∷ [])) = do
    (eP , cP) ← build-path p
    pure ( con (quote NbE.symᵖ) (eP v∷ [])
         , def (quote collapse-sym) (cP v∷ []) )
  build-path (def (quote ++-assoc) (_ h∷ _ h∷ xs v∷ ys v∷ zs v∷ [])) =
    pure ( con (quote NbE.assocᵖ)
             (build-lexp xs v∷ build-lexp ys v∷ build-lexp zs v∷ [])
         , “refl” )
  build-path (def (quote ++-idr) (_ h∷ _ h∷ xs v∷ [])) =
    pure (con (quote NbE.idrᵖ) (build-lexp xs v∷ []) , “refl”)
  build-path (def (quote NbE.flattenˡ) (_ h∷ _ v∷ t₁ v∷ t₂ v∷ t₃ v∷ t₄ v∷ [])) =
    pure ( con (quote NbE.flattenˡᵖ)
             (build-lexp t₁ v∷ build-lexp t₂ v∷ build-lexp t₃ v∷ build-lexp t₄ v∷ [])
         , “refl” )
  build-path (def (quote NbE.flattenʳ) (_ h∷ _ v∷ t₁ v∷ t₂ v∷ t₃ v∷ t₄ v∷ [])) =
    pure ( con (quote NbE.flattenʳᵖ)
             (build-lexp t₁ v∷ build-lexp t₂ v∷ build-lexp t₃ v∷ build-lexp t₄ v∷ [])
         , “refl” )
  build-path (def (quote NbE.flattenᵐ) (_ h∷ _ v∷ t₁ v∷ t₂ v∷ t₃ v∷ t₄ v∷ t₅ v∷ [])) =
    pure ( con (quote NbE.flattenᵐᵖ)
             (build-lexp t₁ v∷ build-lexp t₂ v∷ build-lexp t₃ v∷ build-lexp t₄ v∷
              build-lexp t₅ v∷ [])
         , “refl” )
  build-path (def (quote NbE.bury) (_ h∷ _ v∷ t₁ v∷ t₂ v∷ t₃ v∷ t₄ v∷ [])) =
    pure ( con (quote NbE.buryᵖ)
             (build-lexp t₁ v∷ build-lexp t₂ v∷ build-lexp t₃ v∷ build-lexp t₄ v∷ [])
         , “refl” )
  build-path (def (quote ap) (_ h∷ _ h∷ _ h∷ _ h∷ f v∷ _ h∷ _ h∷ p v∷ [])) =
    build-ap f p
  build-path tm =
    typeError (strErr "list!: cannot quote path\n  " ∷ termErr tm ∷ [])

  -- Sections quote as partial applications when the missing argument is
  -- rightmost — with the bonus that the head argument is NOT under a binder.
  build-ap f@(con (quote List._∷_) (x v∷ [])) p = do
    (eP , cP) ← build-path p
    pure ( con (quote NbE.consᵖ) (x v∷ eP v∷ [])
         , def (quote collapse-ap) (f v∷ cP v∷ []) )
  build-ap f@(con (quote List._∷_) (_ h∷ _ h∷ x v∷ [])) p = do
    (eP , cP) ← build-path p
    pure ( con (quote NbE.consᵖ) (x v∷ eP v∷ [])
         , def (quote collapse-ap) (f v∷ cP v∷ []) )
  -- ◁-whiskers' premise functions must be `eval` of the emitted code (not
  -- the raw section): when the prefix is itself a ++-composite the two
  -- differ by an associativity and are not convertible.
  build-ap (def (quote _++_) (_ h∷ _ h∷ ys v∷ [])) p = do
    (eP , cP) ← build-path p
    pure ( con (quote NbE._◁ᵖ_) (build-lexp ys v∷ eP v∷ [])
         , def (quote collapse-ap)
             ( def (quote NbE.eval) (unknown h∷ unknown v∷ build-lexp ys v∷ [])
             v∷ cP v∷ [] ) )
  build-ap (lam visible (abs _ body)) p = do
    (eP , cP) ← build-path p
    wrap-body body (eP , cP)
    where
      -- Strengthen a term out of the λ-binder (sound because at each layer
      -- the prefix/suffix does not mention the bound variable).
      strip1 : Term → Term
      strip1 = subst-tm (singletonS 0 unknown)

      -- Nested λ-bodies of ∷/++ layers around var 0 (e.g. λ l → xs ++ ys ++ l
      -- or λ l → xs ++ l ++ ys): emit nested cons/whisker codes and layered
      -- collapse-ap premises, with all layer heads strengthened out of the
      -- binder so no meta is ever blocked behind _++_.
      wrap-body : Term → Term × Term → TC (Term × Term)
      wrap-body (var 0 []) pc = pure pc
      wrap-body (con (quote List._∷_) (x v∷ rest v∷ [])) pc = do
        (e , c) ← wrap-body rest pc
        pure ( con (quote NbE.consᵖ) (strip1 x v∷ e v∷ [])
             , def (quote collapse-ap)
                 (con (quote List._∷_) (strip1 x v∷ []) v∷ c v∷ []) )
      wrap-body (con (quote List._∷_) (_ h∷ _ h∷ x v∷ rest v∷ [])) pc = do
        (e , c) ← wrap-body rest pc
        pure ( con (quote NbE.consᵖ) (strip1 x v∷ e v∷ [])
             , def (quote collapse-ap)
                 (con (quote List._∷_) (strip1 x v∷ []) v∷ c v∷ []) )
      wrap-body (def (quote _++_) (_ h∷ _ h∷ var 0 [] v∷ ys v∷ [])) (eP , cP) =
        pure ( con (quote NbE._▷ᵖ_)
                 (eP v∷ build-lexp (strip1 ys) v∷ [])
             , cP )
      wrap-body (def (quote _++_) (_ h∷ _ h∷ ys v∷ rest v∷ [])) pc = do
        (e , c) ← wrap-body rest pc
        pure ( con (quote NbE._◁ᵖ_)
                 (build-lexp (strip1 ys) v∷ e v∷ [])
             , def (quote collapse-ap)
                 ( def (quote NbE.eval)
                     (unknown h∷ unknown v∷ build-lexp (strip1 ys) v∷ [])
                 v∷ c v∷ [] ) )
      wrap-body t _ =
        typeError (strErr "list!: cannot quote whisker body\n  " ∷ termErr t ∷ [])
  build-ap f p =
    typeError (strErr "list!: cannot quote whisker\n  " ∷ termErr f ∷ [])

  dont-reduce : List Name
  dont-reduce =
    quote _∙_ ∷ quote sym ∷ quote ap ∷ quote refl ∷ quote _++_ ∷
    quote ++-assoc ∷ quote ++-idr ∷
    quote NbE.flattenˡ ∷ quote NbE.flattenʳ ∷ quote NbE.flattenᵐ ∷
    quote NbE.bury ∷ []

  list-worker : Term → TC ⊤
  list-worker hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError
              (strErr "list!: goal is not an equation between paths" ∷ [])
    lhs ← normalise lhs
    rhs ← normalise rhs
    (eP , cP) ← build-path lhs
    (eQ , cQ) ← build-path rhs
    let prem = def (quote collapse-eq) (cP v∷ cQ v∷ [])
    unify hole
      (def (quote NbE.solve) (unknown v∷ eP v∷ eQ v∷ prem v∷ []))

  macro
    list! : Term → TC ⊤
    list! = list-worker

open Reflection using (list!) public

-- ============================================================================
-- Tests, Tier A: explicit codes.
-- ============================================================================

private module Tests {o} (X : Type o) (x : X) (xs ys zs ws us vs : List X) where
  open NbE X

  -- A named reassociation against its ∙-free normal form.  Both residues
  -- are definitionally refl (sym refl ≐ refl), so the premise is refl.
  test-flattenʳ : flattenʳ us vs xs ys ≡ sym (++-assoc us vs (xs ++ ys))
  test-flattenʳ =
    solve (flattenʳᵖ [ us ] [ vs ] [ xs ] [ ys ])
          (symᵖ (assocᵖ [ us ] [ vs ] ([ xs ] ⊕ [ ys ])))
          refl

  -- A composite against its collapse: the premise is the corresponding
  -- composite-of-refls equation, closed by a ∙-unit lemma.
  test-∙-collapse : ap (x ∷_) (++-assoc xs ys zs) ∙ refl ≡ ap (x ∷_) (++-assoc xs ys zs)
  test-∙-collapse =
    solve (consᵖ x (assocᵖ [ xs ] [ ys ] [ zs ]) ∙ᵖ idᵖ)
          (consᵖ x (assocᵖ [ xs ] [ ys ] [ zs ]))
          (∙-idr refl)

  -- A two-route square: flattening in two different orders.  Both routes are
  -- ∙ᵖ-composites, so the premise equates two composites of refl.
  test-two-routes
    : flattenˡ zs xs ws ys ∙ ap (λ l → zs ++ xs ++ l) refl
    ≡ flattenˡ zs xs ws ys ∙ refl
  test-two-routes =
    solve (flattenˡᵖ [ zs ] [ xs ] [ ws ] [ ys ] ∙ᵖ ([ zs ] ◁ᵖ ([ xs ] ◁ᵖ idᵖ)))
          (flattenˡᵖ [ zs ] [ xs ] [ ws ] [ ys ] ∙ᵖ idᵖ)
          refl

  -- PathP base-swapping through an arbitrary family: rebase a PathP lying
  -- over flattenʳ onto the sym-of-assoc route.
  test-over
    : ∀ {ℓ} (F : List X → Type ℓ)
      {p : F (us ++ (vs ++ xs ++ ys))} {q : F ((us ++ vs) ++ xs ++ ys)}
    → PathP (λ i → F (flattenʳ us vs xs ys i)) p q
    → PathP (λ i → F (sym (++-assoc us vs (xs ++ ys)) i)) p q
  test-over F =
    over F (flattenʳᵖ [ us ] [ vs ] [ xs ] [ ys ])
           (symᵖ (assocᵖ [ us ] [ vs ] ([ xs ] ⊕ [ ys ])))
           refl

  -- Cast calculus: the ++ []-cancellation round trip.  Cast t forward along
  -- ++-idr and back; fusion turns the tower into one subst along
  -- (idᵖ ∙ᵖ idrᵖ [ xs ]) ∙ᵖ symᵖ (idrᵖ [ xs ]), whose residue collapses.
  module _ {ℓ} (F : List X → Type ℓ) (t : F (xs ++ [])) where
    open Cast F

    test-cast-cancel
      : ⟦ castᵖ (symᵖ (idrᵖ [ xs ])) (castᵖ (idrᵖ [ xs ]) ⟪ t ⟫) ⟧ᶜ ≡ t
    test-cast-cancel =
        reduce (castᵖ (symᵖ (idrᵖ [ xs ])) (castᵖ (idrᵖ [ xs ]) ⟪ t ⟫))
      ∙ solve-cast t ((idᵖ ∙ᵖ idrᵖ [ xs ]) ∙ᵖ symᵖ (idrᵖ [ xs ])) idᵖ
          (∙-idr _ ∙ ∙-idl refl)
      ∙ transport-refl t

-- ============================================================================
-- Tests, Tier B: the same theorems, one token each.
-- ============================================================================

private module MacroTests {o} (X : Type o) (x : X) (xs ys zs ws us vs : List X) where
  open NbE X

  mtest-flattenʳ : flattenʳ us vs xs ys ≡ sym (++-assoc us vs (xs ++ ys))
  mtest-flattenʳ = list!

  mtest-∙-collapse : ap (x ∷_) (++-assoc xs ys zs) ∙ refl ≡ ap (x ∷_) (++-assoc xs ys zs)
  mtest-∙-collapse = list!

  mtest-whiskers
    : flattenˡ zs xs ws ys ∙ ap (zs ++_) (ap (xs ++_) refl)
    ≡ flattenˡ zs xs ws ys ∙ refl
  mtest-whiskers = list!
