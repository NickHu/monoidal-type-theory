# Critical review & refactor of the multicategory/strictification formalisation

Working branch: `refactor`.  Baseline `master` @ 8cf8a7a typechecks cleanly
(all four root modules, ~4s warm).  Every commit on this branch must keep the
repo typechecking (roots: `Multicategory/Instances/Monoidal/Coherence.agda`,
`Multicategory/Strictification/Equivalence.agda`,
`Multicategory/Instances/Category.agda`, and — until deleted — `Monoidal/Free.agda`).

## Ground rules (from the task prompt)

- Trust nothing but Agda's typechecker: not comments, memories, names, or git
  history.  Validate every hypothesis with an Agda experiment.
- Optimise for reading clarity, preferring equational reasoning (1lab style).
  Smaller terms correlate but are not the metric.
- No sacrificing correctness or mathematical generality; reformulation and
  restructuring (including file moves) are allowed and encouraged.
- Work high-level inwards: statements first, then strategy, then implementation.

## Critique of the prompt itself

1. The prompt describes the culmination as "every monoidal category is
   monoidally equivalent to a strict one", but the codebase **never states
   strictness**: `Str-monoidal` is built, and `Comparison` is shown to be a
   strong monoidal functor and an equivalence of underlying categories, but
   there is (a) no definition of *strict monoidal category*, (b) no theorem
   `Str-monoidal is strict`, and (c) no packaged notion of *monoidal
   equivalence* tying (Comparison-monoidal, Comparison-is-equivalence)
   together.  The review treats completing the headline statement as in-scope
   work, not just refactoring.  (In a univalent setting "strict" needs care:
   a reasonable statement is that ⊗ descends from a monoid structure on the
   type of objects, with associator/unitors equal to `path→iso` of the monoid
   paths; when Ob is a set this recovers the classical notion.  1lab's
   `Cat.Strict` (= Ob is a set) is a *different* axis.)
2. The prompt says the formalisation is "of multicategories" — in fact the
   multicategory theory here is exactly as deep as needed for strictification
   (no multicategory functors, no symmetric case).  Fine, but the review
   should not invent scope; generality improvements only in service of the
   existing theorems.

## High-level map of the code (as found)

```
Multicategory.agda                    130   Premulticategory record; list-reassoc paths
Multicategory/Unary.agda               35   underlying category; is-multicategory
Multicategory/Representable.agda      172   is-universal, Representation, is-prop-ness
Multicategory/Instances/Category.agda  56   category → multicategory (degenerate)
Multicategory/Instances/Monoidal.agda 1181  monoidal C → representable multicat (the 4 laws)
Multicategory/Strictification.agda    1580  representable multicat → Str + Str-monoidal
Multicategory/Strictification/Equivalence.agda 71  Str ≃ Unary M
Multicategory/Instances/Monoidal/Coherence.agda 590 Comparison : Str → C strong monoidal equiv
Monoidal/Free.agda + Signature.agda    95   dead exploratory stub (mostly comments)
```

Dependency pipeline: `Monoidal C → (Instances/Monoidal) Mc representable →
(Strictification, abstract) Str-monoidal → (Coherence) Comparison monoidal +
equivalence`.

## Findings log

Classification: **WRONG** (mathematically or textually incorrect claims —
nothing can be *silently* wrong since it typechecks, but comments/names/
statements can mislead or fall short of the claimed theorem) /
**SUBOPTIMAL** (strategy or missed 1lab leverage) / **STYLISTIC**.
Severity H/M/L.  Status: OPEN / VALIDATED (experiment confirms hypothesis) /
FIXED (committed) / REJECTED (experiment refutes; keep as-is, record why).

### Statements & scope

- [F1] **WRONG/H** (statement gap): headline theorem incomplete — no
  `is-strict` predicate, no statement that `Str-monoidal` is strict, no
  packaged "monoidal equivalence".  Plan: define strictness (associator and
  unitors are `path→iso`s of object-type paths coming from a monoid structure
  on Ob), prove it for `Str-monoidal` (should be near-refl: they are *defined*
  as path→isos), and state the final coherence theorem in one place.
  Status: OPEN.
- [F2] **WRONG/L** (comment): `Multicategory.agda` header says "A (non-unital)
  multicategory" but the record has `idₘ` and both unit laws.  Status: OPEN.
- [F3] **SUBOPTIMAL/M**: `Monoidal/Free.agda` + `Monoidal/Free/Signature.agda`
  are an abandoned exploratory stub (constructors and instances commented
  out); unreferenced by everything else.  Plan: delete on this branch
  (recoverable from git history).  Status: OPEN.
- [F4] **OPEN/M**: `is-multicategory = is-category (Unary M)` is defined but
  never used downstream; `Representable.agda`'s is-prop results take
  `is-category (Unary M)` directly.  Decide: use it or drop it.

### Missed 1lab leverage

- [F5] **SUBOPTIMAL/M** (hypothesis): `Representable.agda` hand-rolls
  representing-object uniqueness (restr/restrE/plug-nat/retract/subst-cod,
  ≈ 120 lines).  1lab has `Cat.Functor.Hom.Representable` with
  `Corepresentation`, `corepresentation-unique`, `Corepresentation-is-prop`.
  Hypothesis: package the unary part of `is-universal` as a
  `Corepresentation` of `Homₘ Γ -` : Unary M → Sets and derive
  `Representation-is-prop` from 1lab's.  Needs experiment (the arrow
  component and the non-unary part of `is-universal` must still be handled;
  may not pay off).  Status: OPEN.
- [F6] **SUBOPTIMAL/M**: generic transport-shuffling lemmas proven by J six+
  times (`∘ₘ-substr` ×2 — literally duplicated in Representable and
  Strictification — `∘ₘ-substl`, `∘ₘ-substrG`, `∘ₘ-subst-suf`,
  `subst-dom-cod`, `transp-decomp`).  `∘ₘ-substr` is an instance of
  `∘ₘ-substrG`.  Hypothesis: ONE lemma `∘ₘ-subst` (transport all indices at
  once, by J) subsumes the family; check 1lab for generic subst-naturality
  first.  Status: OPEN.
- [F7] **SUBOPTIMAL/H**: `Strictification.agda` re-proves, for the specific
  universal arrow `⊗-arr Γ`, lemmas `Representable.agda` proves for an
  arbitrary universal arrow (`restrict-nat` vs `plug-nat` — the latter's
  comment even says "Ports Strictification.restrict-nat"; `restrict-equiv` vs
  `restrE`).  Strictification should import and instantiate.  Status: OPEN.

### Strategy-level

- [F8] **SUBOPTIMAL/H**: nine cons-by-cons `path→iso`-characterisation pairs
  in `Instances/Monoidal.agda` (`++-assoc-⊗-iso/-path`, `slot-unbury-iso/-⊗`,
  `assocₘ-flatten-iso/-⊗`, `assocₘ-boundary-iso/-⊗`, `ic-slot₀/₁/₂-iso/-⊗`,
  `ic-flatten-iso/-⊗`, `ic-boundary-iso/-⊗`; ≈ 115 lines of identical
  scaffolding).  All have the shape "path is `ap (a ∷_)`-recursive ⇒ iso is
  `▶.F-map-iso`-recursive".  Hoist one induction principle, or avoid
  pre-characterisation by reworking `subst-⊗-red` call sites.  Status: OPEN.
- [F9] **SUBOPTIMAL/H**: `Strictification.agda`'s `splitμ`, `splitμ-l`,
  `μ-block`, `μ-hex`, `assoc-nat`, `unitor-r-nat`, `μg-collapse`, `μ-unit-r`
  are ≈ 700 lines of raw `subst-∙`/`ap-∙` path algebra.  Look for a
  reformulation that prevents the transports from arising (e.g. a
  transport-absorbed unary composition with its laws proven once, or
  PathP-style reasoning à la 1lab's `Hom-pathp` combinators) rather than
  shuffling them around.  Single biggest readability win available.
  Status: OPEN.
- [F10] **OPEN/M**: the law proofs in `Instances/Monoidal.agda` share a
  "prefix induction over plugs" pattern (`plug-assoc`, `plug-assoc-nil`,
  `plug-shift`, `plug-interchange` all have the same cons-step: plug-cons +
  ▶.F-∘-merge + IH + ▶-assoc/◀-▶-comm naturality + refold).  Candidate: a
  general "an equation between prefix-linear composites holds if it holds at
  []" lemma, or a shared cons-step combinator.  Needs a crisp formulation.
- [F11] **OPEN/M**: `F-α→`/`F-α→-to` + `⊗-context-++-[]-ρ` + `φ-cons` say
  "(⊗-context, φ) is a strong monoidal functor out of the list monoid".
  `Coherence.agda` then *re-assembles* exactly this into
  `Monoidal-functor-on Comparison`.  Consider stating the ⊗-context strong
  monoidal structure ONCE as the organising principle and deriving both the
  law machinery and the Coherence assembly from it.  Needs design: the domain
  would be `Str-monoidal` itself (making `Comparison-monoidal` the master
  statement and `F-α→` its unfolding) — check circularity carefully.
- [F12] **OPEN/L**: `Premulticategory` law statements mix PathP (outer) with
  `subst` (inner).  Explore a uniform formulation (e.g. composition along a
  decomposition path) — only worth it if instances demonstrably simplify.

### Local / stylistic

- [F13] **STYLISTIC/M**: inconsistent naming across files (`plug-nat` vs
  `restrict-nat`; `dec`/`gfi` remnants in comments; helper aliases `φ`/`ψ`
  used with different meanings in different scopes).  Unify after structural
  refactors.
- [F14] **OPEN/M**: `Strictification/Equivalence.agda` (Str ≃ Unary M) and
  `Coherence.agda`'s `Comparison` (Str → C) overlap: for the monoidal
  instance, `Unary Mc` is C-with-unit-padded-homs.  Check whether Reindex ∘
  (Unary Mc ≅ C) subsumes the ff/eso part of Coherence, leaving only the
  monoidal structure there.
- [F15] **STYLISTIC/L**: `Instances/Category.agda` fine as-is.
- [F16] **STYLISTIC/L**: `docs/1lab-reasoning-cheatsheet.md` and `CLAUDE.md`
  describe pre-rename state in places; refresh at the end.

## Verified facts (Agda-checked or read from 1lab source, this session)

- Baseline typecheck of all four roots: OK (exit 0), ~4 s with warm `_build`.
- 1lab has **no** multicategory/operad development and **no** monoidal
  strictification (grep over `src/`): the core content here is genuinely not
  upstream.
- 1lab `Cat.Functor.Hom.Representable` provides `Corepresentation`,
  `corepresentation-unique`, `Corepresentation-is-prop` (needs
  `is-category C`).
- 1lab `Cat.Monoidal.Functor` provides `Lax-monoidal-functor-on`,
  `Monoidal-functor-on` (used by Coherence already); no monoidal-equivalence
  notion upstream.
- 1lab `Cat.Strict` = "Ob is a set"; different axis from monoidal strictness.

## TODO / plan (keep current; tick items only when actually done & committed)

Phase 0 — setup
- [x] Read all project files end-to-end.
- [x] Baseline typecheck.
- [x] Branch `refactor`, this REVIEW.md.

Phase 1 — fact-finding (parallel agents; results land in this file)
- [ ] 1lab leverage survey (transport/PathP combinators in 1Lab.Path &
      Cat.Reasoning; Hom-pathp family; monoidal reasoning combinators;
      Cat.Bi.Reasoning exports; list-monoid material).
- [ ] Per-file deep audits with concrete simplification hypotheses:
      (a) Multicategory.agda + Unary + Representable;
      (b) Instances/Monoidal.agda;
      (c) Strictification.agda;
      (d) Coherence.agda + Equivalence.agda.
- [ ] Design for F1 (strictness statement).

Phase 2 — statement-level fixes (before detail work)
- [ ] F1: is-strict + final theorem statement.
- [ ] F2: fix header comment.
- [ ] F3: delete Monoidal/Free*.
- [ ] F4: resolve is-multicategory usage.

Phase 3 — deduplication & leverage (each its own commit, typecheck gate)
- [ ] F7: Strictification imports Representable's general lemmas.
- [ ] F6: one transport-lemma family.
- [ ] F5: Corepresentation experiment (adopt or REJECT with reasons).
- [ ] F8: one induction principle for the path→iso characterisations.

Phase 4 — the big rewrites (design first, then implement)
- [ ] F9: Strictification transport-algebra rework.
- [ ] F10: prefix-induction factoring in Instances/Monoidal.
- [ ] F11: ⊗-context-as-strong-monoidal-functor reorganisation (+ F14).
- [ ] F12: law-formulation experiment (only if F10/F11 point that way).

Phase 5 — polish
- [ ] F13 naming pass; F15; F16 docs refresh; final CLAUDE.md update.
- [ ] Full clean-cache typecheck (`rm -rf _build` timing run) to check
      performance didn't regress beyond tolerance.

## Session log

- **2026-07-23 (session 1)**: read everything; baseline OK; branch created;
  REVIEW.md written; initial 1lab survey (no upstream multicats or
  strictification; Corepresentation machinery exists).  Next: parallel deep
  audits (Phase 1), then Phase 2.
