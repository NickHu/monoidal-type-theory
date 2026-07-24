# Shulman's simple type theory for monoidal categories — formalisation notes

Investigation of formalising Figure 2.2 of Mike Shulman's *Categorical logic
from a categorical point of view* (draft; §2.4.2, pp. 106–110) over this
repository's multicategory development.  The core is
`Multicategory/Free.agda` (syntax, substitution, β/η-congruence), with the
laws, representability, strictification, freeness and uniqueness in the
`Multicategory/Free/*` modules; this note records the design mapping, the
findings, and the (now completed) roadmap to Theorem 2.4.10.

## Source correction

Figure 2.2's **1E** rule reads

    Ψ ⊢ M : 1        Γ,Δ ⊢ N : A
    ─────────────────────────────
     Γ,Ψ,Δ ⊢ match1(M,N) : C

The premise's `A` and the conclusion's `C` must agree; Figure 2.4 (p. 111)
restates the rule with premise `Γ,Δ ⊢ N : C`, which is the intended reading
and the one formalised.

## Design mapping

| Shulman | Formalisation |
|---|---|
| multigraph G (§2.2) | `Multigraph` record: `Ob : Type o`, `Hom : List Ob → Ob → Type h` — no set-level assumptions, matching the repo invariant |
| types `⊢ A type` | `data Ty`: `base`, `_⊗_`, `𝟙` |
| contexts | `Ctx = List Ty` — same as `Premulticategory` contexts |
| terms / derivations | intrinsic mutual family `Tm : Ctx → Ty → Type`, `Sp : Ctx → List G.Ob → Type` (spines = the n premises of the generator rule, contexts concatenated) |
| Lemma 2.4.7 (linearity) | vacuous: contexts are indices, every variable is a structural position |
| Lemma 2.4.8 (unique derivations) | vacuous: terms *are* derivations |
| the `Γ\|Δ` annotation on `match⊗` | the constructor's implicit context arguments `{Γ} {Δ}` — and Agda *demands* them wherever the checker would otherwise face `Γ ++ Δ ≟ …` (`++` is not injective), a striking mechanisation of Shulman's remark that the annotation is what makes type-checking unique |
| substitution (Fig. 2.3, Lemma 2.4.9) | `sub : Split x Θ Ρ Ξ → Tm Ρ z → Tm Γ x → Tm (Θ ++ Γ ++ Ξ) z` — the same type as `Premulticategory._∘ₘ_` |
| "?[M/x] cannot happen" | `split-[] : Split x Θ [] Ξ → ⊥` |
| β/η (p. 109) | `_≈_` inductive congruence; hom-sets are `Tm Γ z / _≈_` |
| Theorem 2.4.6/2.4.10 multicategory | `Free/Identity`, `Free/Assoc`, `Free/Interchange`, `Free/Congruence*`, assembled in `Free/Multicategory` |
| representability | `Free/Representable`; β⊗/η⊗ are literally the two round-trips of the universality equivalence at `⦅var,var⦆` |
| Exercise 2.4.1 | already done abstractly by `Multicategory.Strictification` + `Instances/Monoidal/Coherence` |

The slot of a substitution is witnessed by the structural datatype

    data Split (x : Ty) : Ctx → Ctx → Ctx → Type o where
      here  : Split x [] (x ∷ Ξ) Ξ
      there : Split x Θ Ρ Ξ → Split x (a ∷ Θ) (a ∷ Ρ) Ξ

(`Split x Θ Ρ Ξ` ⇔ `Ρ = Θ ++ x ∷ Ξ`) rather than by a path, so `sub` recurses
on it, folds reduce through it, and neither decidability of `Ty` nor any
set-level assumption is needed.  `split-++` decides which side of a
concatenation a slot falls in — by recursion on the left part and the split,
*not* by comparing types — which is what makes the `⦅_,_⦆`/`match⊗`/spine
cases of `sub` go through.  Result contexts are reconciled by cons-by-cons
reassociation paths (`flattenˡ/ʳ/ᵐ`, `bury`), per the repo discipline.

## Findings

1. **Context arithmetic of β/η.**  η⊗, β𝟙, η𝟙 are *homogeneous* — both sides
   have definitionally equal context indices, because `++` computes on the
   literal lists `A ∷ B ∷ []` and `[]` (e.g. `N[⦅x,y⦆/u]` lives in
   `Γ ++ (A ∷ B ∷ []) ++ Δ ≡ᵈᵉᶠ Γ ++ A ∷ B ∷ Δ`).  Only β⊗ needs a transport,
   along the structural `β⊗-boundary` — the same pattern as `assocₘ` in
   `Multicategory.agda`.

2. **Match the term first.**  Defining `sub` by splitting on the `Split`
   before the term strands coverage on `Γ ++ Δ ≟ x ∷ Ξ`.  The `var` and `⋆`
   cases therefore delegate to helpers (`sub-var`, `split-[]`) that analyse
   the split *after* the term constructor has fixed the context's shape.

3. **Without-K subtlety.**  A helper of type `Split x Θ (x ∷ []) Ξ` (slot
   type and singleton type the *same* variable) is unmatchable without K
   (reflexive `x ≟ x`).  Keeping them distinct — `Split x Θ (z ∷ []) Ξ`,
   with `here` unifying `x := z` — is fine.  All of `Tm`'s constructors
   target fully general indices built from their arguments, so indexed
   matching stays in the without-K-friendly fragment (no transp-litter from
   `-W noUnsupportedIndexedMatch` observed).

4. **Frozen-meta gotcha** (cost real time): an unannotated `∀`-binder whose
   type is constrained only through `_++_`/`≡` (e.g.
   `flattenˡ : ∀ Θ Γ Ξ₁ Δ → (Θ ++ Γ ++ Ξ₁) ++ Δ ≡ …`) gets a fresh type
   meta that nothing ever pins down; it freezes unsolved and every later
   *use* of the lemma then fails with reflexive-looking constraints
   `X = X : List Ty (blocked on _N)` reported far from the culprit.
   Annotate: `∀ (Θ Γ Ξ₁ Δ : Ctx) → …`.

5. **Infrastructure fit.**  `sub`'s type is exactly `_∘ₘ_`; `sub`'s `var`
   clause is a transport along `sym (++-idr Γ)`, which is exactly the
   boundary of the `idₘr` field — the syntactic multicategory's right
   identity law should be a `transport-filler`.  `Strictification` consumes
   precisely `Premulticategory` + `is-representable`, so a strict monoidal
   category strictifying `FMonCat G` is obtained by composition with
   existing code (`Free/Strict`).

## Original roadmap (all items now complete — see Status)

1. **Descend `sub` to the quotient.**  `cast-≈` (transport a `_≈_` proof
   along a context path), then `sub-≈ˡ`/`sub-≈ʳ` by mutual induction with
   spines, then `_∘ₘ_ = Quot-op₂ …` (`Data.Set.Coequaliser`).

2. **Premulticategory laws.**  `idₘl` (plug `var` into a slot — homogeneous),
   `idₘr` (transport-filler), then `assocₘ` and `interchangeₘ` = Lemma
   2.4.9's associativity/interchange, by induction on the outer term.  These
   are the transport-heavy inductions; the `∘ₘ-subst`/`∘ₘ-pathp` kit and the
   "plug arrows into a PathP before ∙P-composing" rule from
   `Strictification` apply.  Yields `FMonCat G : Premulticategory`.

3. **Representability.**  `⦅var,var⦆ : Homₘ (A ∷ B ∷ []) (A ⊗ B)` is
   universal: the inverse of `(- ∘ₘ ⦅var,var⦆)` is `match⊗(var, -)`, with
   round trips β⊗ (after the substitution clauses reduce `match⊗`'s
   scrutinee position) and η⊗; likewise `⋆` for `𝟙`.  N-ary universal
   arrows by induction on the context (universal arrows compose — or
   directly, iterated `match`).  Gives `is-representable (FMonCat G)`,
   hence via `Strictification` a strict monoidal category strictifying
   `FMonCat G`.

4. **Freeness (Theorem 2.4.10).**  For `M` representable and `P : G → M` a
   multigraph map: interpret `Ty` by folding `M`'s chosen representations,
   `Tm/Sp` by recursion (Shulman's order: first terms, then
   substitution-to-composition, then `_≈_`), descend to the quotient, and
   prove uniqueness by term induction.  This is the largest item and needs a
   notion of multifunctor (now `Multicategory/Functor.agda`).

Items 1–2 are mechanical but transport-heavy (comparable to the
`Instances/Monoidal` law proofs); item 3 is short once 1–2 exist; item 4 is
a paper's-worth of induction but routine.

## Status

Everything — through Theorem 2.4.10's freeness and the uniqueness of the
extension — is **done and machine-checked** (no postulates anywhere):

- `Free/Kit`, `Free/SplitLemmas` — transport kit ("sub under the interval",
  never J) and the split coherence pack; `Split-++` is now a *view with
  soundness* (each branch carries a PathP reconstituting the analysed split),
  and `sub` dispatches to named branch handlers, so proofs never fight
  `with`-abstraction.
- `Free/Identity`, `Free/Assoc`, `Free/Interchange` — Lemma 2.4.9 in full:
  identity, associativity and interchange of substitution, as PathPs over
  the same boundary paths as the `Premulticategory` record fields.
- `Free/CongruenceLeft`, `Free/RedexStability`, `Free/CongruenceRight` —
  `sub` respects `_≈_` on both sides; the β/η cases are standalone redex
  stability lemmas (no induction hypothesis), each a composition of
  assoc/interchange instances.
- `Free/Multicategory` — `FMonCat G : Premulticategory`: hom-sets `Tm Γ z / ≈`,
  composition `Quot-op₂` of `sub` at the canonical split; the four laws
  descend along the composite-split coherences (`unbury-split`,
  `slot₀/₁-split`) with `inc` applied under the interval.
- `Free/Representable` — `FMonCat-rep : is-representable (FMonCat G)`:
  `⦅var,var⦆`/`⋆` universal via the β/η round-trips, n-ary arrows by
  induction with the new abstract `universal-∘ₘ` (Representable.agda).
- `Free/Strict` — `FreeStrict(-monoidal, -is-strict)`: a strict monoidal
  category obtained by strictifying `FMonCat G` via the existing Hermida
  strictification.  Monoidally it plays the role of the free monoidal
  category on G, but no universal property is proven for it (and strict
  1-categorical freeness would fail for this object — its objects are all
  contexts `List Ty`, not lists of generators).
- `Free/Eval` — evaluation into any representable premulticategory
  (`Multigraph-hom↓`, `⟦_⟧ᵗ`, `eval`); `Multicategory/Functor.agda` defines
  multifunctors.
- `Free/Freeness` — the freeness half of Theorem 2.4.10: `eval-sub`
  (evaluation maps substitution to `_∘ₘ_`), `eval-≈` (β/η go to the
  universality equivalences), and descent to `Multifunctor (FMonCat G) M`.
- `Free/Uniqueness` — the extension is unique: any multifunctor
  `FMonCat G → M` agreeing with the generators and preserving the chosen
  representability data is the evaluation multifunctor.

Proof-engineering notes that made this tractable: the soundness-carrying
view; handler-based `sub`; all reassociation paths structural cons-by-cons
with named "δ-lemma" squares relating them; laws stated over composite
splits so the record's `subst`-transports bridge via three small split
coherences; `inc`/`sub`/`≈` applied under the interval instead of J,
everywhere.
