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
  VALIDATED (Scratch/E1.agda, typechecks): `is-strict-monoidal` record =
  (α/λ/ρ object-type paths) + (descent: α→/λ←/ρ← ≡ path→iso legs) +
  (path-level pentagon & triangle — REQUIRED on non-set Ob to make the
  object monoid coherent; automatically satisfiable when Ob is a set,
  proven as `set→is-strict-monoidal`).  `Str-is-strict` for ANY representable
  multicategory via one J-bridge `path-to {Str} p ≡ ≅to (ap ⊗₀ p)`;
  α-path = ++-assoc, λ-path = refl, ρ-path = ++-idr; path-pentagon needs a
  fresh α→-direction `++-pentagon→` spine induction.  Headline Σ-statement
  assembles from existing exports.  Bonus identified: a generic
  "coherent path-monoid ⇒ monoidal structure" constructor could DERIVE
  Str-monoidal's triangle/pentagon fields (~45 lines of ap-∙ shuffling)
  from path-triangle/path-pentagon.  Status: VALIDATED.
- [F2] **WRONG/L** (comment): `Multicategory.agda` header says "A (non-unital)
  multicategory" but the record has `idₘ` and both unit laws.  Status: OPEN.
- [F3] **SUBOPTIMAL/M**: `Monoidal/Free.agda` + `Monoidal/Free/Signature.agda`
  are an abandoned exploratory stub (constructors and instances commented
  out); unreferenced by everything else.  Deleted on this branch (recoverable
  from git history).  Status: FIXED.
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
  `Representation-is-prop` from 1lab's.  VALIDATED (Scratch/A2.agda): pays
  off — `HomΓ : List Obₘ → Functor (Unary M) (Sets h)` (with F-∘ = plug-nat
  at an ARBITRARY u, exposing that plug-nat is functoriality — universality
  not needed), `Rep→Corep`, then `Representation-is-prop` via 1lab's
  `Corepresentation-is-prop`; deletes `retract` and `subst-cod` (both
  bespoke univalence arguments).  ≈ −10 lines net, big leverage win.
  Status: VALIDATED.
- [F6] **SUBOPTIMAL/M**: generic transport-shuffling lemmas proven by J six+
  times (`∘ₘ-substr` ×2 — literally duplicated in Representable and
  Strictification — `∘ₘ-substl`, `∘ₘ-substrG`, `∘ₘ-subst-suf`,
  `subst-dom-cod`, `transp-decomp`).  `∘ₘ-substr` is an instance of
  `∘ₘ-substrG`.  VALIDATED (Scratch/A1.agda): ONE `∘ₘ-subst` (all indices at
  once) subsumes the family, provable WITHOUT J — it is `_∘ₘ_` applied under
  the interval to transport-fillers; all five original statements derive in
  ≤2 lines.  1lab has no generic subst-application lemma (survey).
  Status: VALIDATED.
- [F7] **SUBOPTIMAL/H**: `Strictification.agda` re-proves, for the specific
  universal arrow `⊗-arr Γ`, lemmas `Representable.agda` proves for an
  arbitrary universal arrow (`restrict-nat` vs `plug-nat` — the latter's
  comment even says "Ports Strictification.restrict-nat"; `restrict-equiv` vs
  `restrE`).  Strictification should import and instantiate.  VALIDATED
  (Scratch/A5.agda, Scratch/C1.agda): `S.restrict ≡ Rep.restr M (⊗-arr Γ)`
  by refl; `Rep.plug-nat M (⊗-arr Γ)` inhabits `restrict-nat`'s type as a
  drop-in; `∘ₘ-substr` verbatim-identical.  ≈ −55 lines.  Status: VALIDATED.

### Strategy-level

- [F8] **SUBOPTIMAL/H**: nine cons-by-cons `path→iso`-characterisation pairs
  in `Instances/Monoidal.agda` (`++-assoc-⊗-iso/-path`, `slot-unbury-iso/-⊗`,
  `assocₘ-flatten-iso/-⊗`, `assocₘ-boundary-iso/-⊗`, `ic-slot₀/₁/₂-iso/-⊗`,
  `ic-flatten-iso/-⊗`, `ic-boundary-iso/-⊗`; ≈ 115 lines of identical
  scaffolding).  All have the shape "path is `ap (a ∷_)`-recursive ⇒ iso is
  `▶.F-map-iso`-recursive".  Naive route REFUTED (Scratch/B1refute.agda:
  helper paths do NOT equal `ap (Θ ++_)` of their base — endpoints differ as
  neutral terms).  Working design VALIDATED (Scratch/B1.agda): a record
  `⊗-chain p` bundling {⊗iso; char : path→iso (ap ⊗-context p) ≡ ⊗iso} with
  combinators chain-refl / chain-∷ / chain-sym (record, not Σ — needed for
  inference; eta keeps projections reducing; chain-sym absorbs the inner
  recursions and makes `flat-from` refl).  ≈ −87 lines.  Status: VALIDATED.
- [F9] **SUBOPTIMAL/H**: `Strictification.agda`'s `splitμ`, `splitμ-l`,
  `μ-block`, `μ-hex`, `assoc-nat`, `unitor-r-nat`, `μg-collapse`, `μ-unit-r`
  are ≈ 700 lines of raw `subst-∙`/`ap-∙` path algebra.  Look for a
  reformulation that prevents the transports from arising (e.g. a
  transport-absorbed unary composition with its laws proven once, or
  PathP-style reasoning à la 1lab's `Hom-pathp` combinators) rather than
  shuffling them around.  Single biggest readability win available.
  VALIDATED (Scratch/C2.agda + Scratch/C3.agda): kit = `∘ₘ-pathp` (free
  heterogeneous congruence — `_∘ₘ_` under the interval), `hom-over` (base
  path reconciliation), `ic₂` (binary interchange with all transport junk
  absorbed once, HOMOGENEOUS statement), `assocˢ/ᵘ` wrappers.  Measured:
  μ-block 45→4, swap-eq 33→5, μg-collapse 47→3, eqΓ 10→1, full splitμ
  113+83dep → ~99 readable lines.  Caveat: plug arrows into PathP segments
  BEFORE ∙P-composing (∙-composites are hcomps, not cons-headed).
  Estimated ≥ 250 lines saved.  Status: VALIDATED.
- [F10] **OPEN/M**: the law proofs in `Instances/Monoidal.agda` share a
  "prefix induction over plugs" pattern (`plug-assoc`, `plug-assoc-nil`,
  `plug-shift`, `plug-interchange` all have the same cons-step: plug-cons +
  ▶.F-∘-merge + IH + ▶-assoc/◀-▶-comm naturality + refold).  Candidate: a
  general "an equation between prefix-linear composites holds if it holds at
  []" lemma, or a shared cons-step combinator.  VALIDATED (Scratch/B2.agda):
  `▶-∘₄` (4-factor whisker distribution) + `cons-step` (IH + one naturality
  square → whole cons case) + `▶-weave₄`; plug-shift re-proved 39→15 lines,
  plug-interchange cons 45→12.  ≈ −100 lines over the four inductions.
  Status: VALIDATED.
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

### Further findings from the audit fan-out (2026-07-23)

- [F17] **SUBOPTIMAL/M** VALIDATED (Scratch/A3.agda): a subst-free
  "PathP-graph" formulation of assocₘ/interchangeₘ (quantify over the
  reshaped composite + a PathP witnessing it) is interderivable with the
  current fields and kills the `transport-refl` fixups at every degenerate-
  context consumer (Unary.assoc, restrict-nat's e0, eqΓ, …).  Porting
  touches all instances; adopt only if the C2/B-refactors leave the fixups
  visible.  DEFERRED for now.
- [F18] **SUBOPTIMAL/M** VALIDATED (Scratch/A4.agda): three list-reassoc
  helpers (`interchange-slot₀/₂`, `interchange-flatten`) are definitionally
  `sym ∘ ++-assoc` / `++-assoc` instances (both clauses refl); alias them,
  keeping names.  −12 lines + downstream characterisation mergers.
- [F19] **SUBOPTIMAL/M** VALIDATED (Scratch/B3.agda): idₘl/idₘr machinery
  shrinks 4–6× with functor-reasoning combinators (▶.annihilate, ▶.pulll,
  ▶.cancell, cancell/pulll): plug-ρ 26→4, intro-eq 15→4, unit-cancel 15→2,
  plug-unit-core 35→11.  Also `Hom-pathp-refll C` subsumes the
  to-pathp+transport-⊗-red discharge of all three PathP laws (idₘr' proven).
  Keep F-α→'s display-style cons proof (mathematical heart).
- [F20] **SUBOPTIMAL/M** VALIDATED (Scratch/B4.agda): `F-α→-to` is a 4-line
  corollary of `F-α→` via `Cat.Reasoning.swizzle` + ▶/◀.cancel; the 32-line
  QS/MID/hexagon-to manual inversion goes.  −30 lines.
- [F21] **SUBOPTIMAL/L**: dead code in Strictification (`arr-nat`,
  `≅from-refl`, `◀-bridge`, `▶-bridge`, ~21 lines, grep-verified unused) and
  a dead `import Cat.Bi.Solver` in Instances/Monoidal (grep-verified).
- [F22] **INFO/M** (C5 inventory): only 13 Strictification names are
  consumed downstream (Str, ⊗₀, ⊗-arr, ⊗-arr-univ, μ, _⊗ₛ_, ⊗ₛ-μ,
  restrict₂-equiv, restrict₂-μ, Str-monoidal, ≅to, ≅to-refl, ≅from-to) —
  everything else is free to reshape/privatise.
- [F23] **WRONG/L** VALIDATED: three Strictification comments falsely claim
  `is-set` usage (lines ~293, ~322, ~596-599 describe abandoned strategies;
  the proofs beneath use spine lemmas / homotopy-natural / apd — NO is-set
  anywhere in the file).  Also Multicategory.agda:109 mislabels assocₘ "the
  pentagon", and Representable's restr/plug-nat docstrings claim universality
  is needed when it is not.
- [F24] **SUBOPTIMAL/H** VALIDATED (Scratch/D3.agda): Coherence's `bundle`
  121→~30 lines by rewriting both plug legs with the already-exported
  `plug-id`/`Piso` upfront (pure-iso induction remains; `Piso` must join the
  Repr using-list).
- [F25] **SUBOPTIMAL/M** VALIDATED (Scratch/D1/D5.agda): `tri←` is verbatim
  1lab `Cat.Bi.Reasoning.triangle-inv` (at Deloop M₀); `step-a` is
  `-⊗-.rlmap`; `ρ-whisker-collapse-to-φ` = pulll rlmap ∙ cancelr
  (▶.annihilate); `φ≡μ` 9→2 lines; `ρ←-reindex` 22→6; one shared
  `(⊗-context-++ Γ []).to ≡ ρ→ ∘ (⊗-context-++-idr Γ).to` lemma serves four
  sites (−30 lines).
- [F26] **SUBOPTIMAL/M** VALIDATED (Scratch/D2.agda): `Comparison` factors
  definitionally through Equivalence.agda's `Reindex`:
  `Unwrap : Functor (Unary Mᵣ) C` (an independently meaningful equivalence
  "Unary of the representable multicat of C is C") with
  `Comparison ≡ Unwrap F∘ Reindex` by `Functor-path refl refl`.  Line-
  neutral in Coherence but makes Equivalence.agda load-bearing.  Adopt by
  DEFINING Comparison as the composite (F₁ still reduces definitionally).
- [F27] **SUBOPTIMAL/M** VALIDATED (Scratch/D4.agda, Scratch/E1.agda): the
  headline theorem packaged as
  `monoidal-strictification : Σ Cˢ, Σ Mˢ, is-strict-monoidal Mˢ ×
   Σ F : Cˢ → C, Monoidal-functor-on × is-equivalence` — assembles from
  existing exports; 1lab has nothing to reuse for "monoidal equivalence".
- [F28] **STYLISTIC/M** (B5): Instances/Monoidal conflates a reusable
  ⊗-context/plug toolkit (~400 lines; exactly what Coherence imports) with
  the law proofs (~500 lines post-refactor).  Option: split into
  `…/Monoidal/Tensor.agda` + laws; or mark law-machinery private.  Decide
  during implementation.
- [F29] **INFO** (survey highlights for implementation): `Cat.Univalent`'s
  Hom-pathp/-refll/-reflr family is the idiomatic discharge for
  Hom-over-object-path goals; `1Lab.Path.Reasoning` (∙-pulll/∙-swapl/
  ∙-cancelsl/⟩∙⟨) mechanises the hand-fought list-path coherences
  (++-pentagon, splitμ-inner, idr-assoc-coh); 1lab has NO ≡[]-style
  dependent-path reasoning syntax (idioms: to/from-pathp, ◁/▷, ∙P,
  Hom-pathp); `Regularity.reduce!/precise!` can kill transport-refl noise;
  MonR (Cat.Monoidal.Reasoning) does NOT re-export triangle-ρ→/λ→≡ρ→/
  triangle-inv (those need the Cat.Bi.Reasoning open); Data.List.Properties
  has no nil-reindex/naturality/pentagon lemmas (spine block stays local).

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
- [x] 1lab leverage survey (see F29; full catalogue in the workflow journal).
- [x] Per-file deep audits — all done, 19 scratch modules under `Scratch/`
      (A1-A5, B1-B4 + B1refute, C1-C3, D1-D5, E1), every hypothesis
      validated or refuted by the typechecker.
- [x] Design for F1 (strictness statement) — Scratch/E1.agda typechecks.

Implementation order (dependency-driven):
1. Multicategory.agda: F2/F23 comments, ∘ₘ-subst (F6), helper aliases (F18),
   hoist shared spine lemma(s).  [me]
2. Representable.agda: A2/F5 Corepresentation rewrite, docstrings, F4.  [me]
3. Monoidal/Strict.agda (new): is-strict-monoidal + set→is-strict
   (+ possibly the generic path-monoid⇒monoidal constructor).  [me]
4. In parallel: Instances/Monoidal.agda (F8/F10/F19/F20/F21/F28) ∥
   Strictification.agda (F7/F9/F21/F22/F23 + Str-is-strict).  [agents]
5. Coherence.agda + Equivalence.agda: F24/F25/F26/F27 + headline.  [agent/me]
6. Polish: F13/F16, delete Scratch/, clean-cache timing run.

Phase 2 — statement-level fixes (before detail work)
- [x] F1: is-strict + final theorem statement (commit 7f4d061:
      Monoidal/Strict.agda, Str-is-strict in Strictification,
      monoidal-strictification in Coherence).
- [x] F2: fix header comment (7db435e).
- [x] F3: delete Monoidal/Free* (a6a7114).
- [x] F4: Representable's univalence hypothesis is now is-multicategory M
      (731e681).

Phase 3 — deduplication & leverage (each its own commit, typecheck gate)
- [~] F7: Strictification dedup — in progress (rewrite agent).
- [x] F6: ∘ₘ-subst + ++-assoc-nil shared in Multicategory (7db435e);
      Representable migrated (731e681); Strictification migration in the
      rewrite agent.
- [x] F5: Corepresentation rewrite of Representable (731e681, −9 lines,
      removes retract/subst-cod/Univalent machinery).
- [x] F18: three helpers aliased to ++-assoc (7db435e).
- [~] F8: ⊗-chain refactor — in progress (rewrite agent).

Phase 4 — the big rewrites (design first, then implement)
- [~] F9: Strictification PathP-kit rework — in progress (rewrite agent,
      spec = validated Scratch/C1-C3 + dead-code F21 + comments F23).
- [~] F10/F19/F20: Instances/Monoidal rework — in progress (rewrite agent,
      spec = validated Scratch/B1-B4).
- [ ] F11: ⊗-context-as-strong-monoidal-functor reorganisation (+ F14) —
      assess after the rewrites land.
- [ ] F12/F17: law-formulation change — DEFERRED unless post-rewrite noise
      justifies it.

Phase 5 — polish
- [ ] F13 naming pass; F15; F16 docs refresh; final CLAUDE.md update.
- [ ] Full clean-cache typecheck (`rm -rf _build` timing run) to check
      performance didn't regress beyond tolerance.

## Session log

- **2026-07-23 (session 1)**: read everything; baseline OK; branch created;
  REVIEW.md written; initial 1lab survey (no upstream multicats or
  strictification; Corepresentation machinery exists).  Audit fan-out (6
  agents, 19 typechecked scratch modules) — all major hypotheses validated,
  one refuted (B1 naive route).  Commits: 9647524 (plan), a6a7114 (F3),
  a33d8ec (audit results), 7db435e (Multicategory base), 731e681
  (Representable/Corepresentation), 7f4d061 (F1 headline theorem).  Two
  rewrite agents launched in parallel on Instances/Monoidal.agda and
  Strictification.agda (specs in the Phase-4 items; validated scratch as
  source).  After they land: cross-check all roots, commit, then
  Coherence/Equivalence pass (F24-F27), then polish.

## Decisions on remaining strategy items (post-rewrite assessment)

- [F11] REJECTED (reorganisation): the strong-monoidal-functor content of
  ⊗-context is already stated exactly once (F-α→ + unit lemmas in
  Instances/Monoidal) and consumed twice (the assocₘ machinery via F-α→-to,
  and Coherence's Monoidal-functor-on assembly).  Making Coherence's record
  the master statement would invert the dependency direction (Instances/
  Monoidal cannot import Coherence).  Current organisation is correct.
- [F12/F17] REJECTED (law reformulation): the PathP kit (assoc₀₀-family,
  Hom-pathp-refll discharge, ∘ₘ-pathp) has absorbed the transport-refl noise
  at every consumer that motivated the reformulation; changing the record
  fields now would churn all instances for no measurable gain.
- [F14] RESOLVED via F26 (in flight): Equivalence.agda becomes load-bearing
  by defining Comparison = Unwrap F∘ Reindex.
- [F28] REJECTED (file split): post-refactor Instances/Monoidal.agda is 986
  lines with a clearly-sectioned toolkit/laws boundary; a physical split
  would churn module paths for marginal gain.  The reuse boundary is
  documented by Coherence's using-list.

## Final status summary (end of session 1)

All planned work is DONE except items explicitly REJECTED above.  Findings:
F1-F10, F18-F27 FIXED (commits below); F11/F12/F17/F28 REJECTED with reasons;
F13 folded into the rewrites (naming made consistent as files were touched);
F15 no-op; F16 done (CLAUDE.md rewritten; cheatsheet checked, still accurate).
The `Scratch/` validation modules (never committed) are deleted — they
validated designs against the PRE-refactor code and are recorded per-finding
above; the refactored code itself is now the evidence.

Line counts (before → after, excluding REVIEW.md/docs):
```
Multicategory.agda                       130 → 163  (+∘ₘ-subst, ++-assoc-nil)
Multicategory/Unary.agda                  35 → 35
Multicategory/Representable.agda         172 → 163  (Corepresentation leverage)
Multicategory/Instances/Category.agda     56 → 56
Multicategory/Instances/Monoidal.agda   1181 → 986
Multicategory/Strictification.agda      1580 → 1369 (incl. +Str-is-strict)
…/Strictification/Equivalence.agda        71 → 77   (now load-bearing)
…/Instances/Monoidal/Coherence.agda      590 → 484  (incl. +headline theorem)
Monoidal/Free* (dead)                     95 → 0
Monoidal/Strict.agda                       0 → 87   (NEW: strictness predicate)
total                                   3910 → 3420
```
Net −490 lines while ADDING the previously-missing strictness predicate,
Str-is-strict, the packaged headline theorem, the HomΓ/corepresentation
bridge, and three reusable proof kits (⊗-chain, cons-step, the PathP kit).

Commit sequence (each typechecks): 9647524 plan · a6a7114 F3 · a33d8ec audit
results · 7db435e Multicategory base · 731e681 Representable · 7f4d061 F1
headline · dedd39b/62e35d7 bookkeeping · 4d8845a Instances/Monoidal rewrite ·
91f7457 Strictification rewrite · 4d9437c Coherence/Equivalence rewrite ·
(this commit) polish + docs.

Possible future work (deliberately not done):
- Generic "coherent path-monoid + natural transports ⇒ monoidal structure"
  constructor in Monoidal/Strict.agda, deriving Str-monoidal's
  triangle/pentagon fields from path-triangle/path-pentagon (would delete
  ~45 more lines of ap-∙ shuffling in Strictification and give the converse
  direction of the strictness story).  Sketched in the F1 design notes.
- η-arr and restrict₂-nat keep small subst cores (kit-resistant for reasons
  documented inline); a two-parameter dom+cod PathP composition helper would
  clean them if ever needed elsewhere.
- Upstreaming candidates for 1lab: path→iso-sym, is-strict-monoidal,
  triangle-inv usage patterns; the multicategory development itself.

## Follow-up (session 2, 2026-07-23): from-path-monoid constructor

Implemented the previously-noted future-work item: the generic
"coherent path-monoid ⇒ monoidal structure" constructor.

- `Monoidal/Strict.agda` (+185 lines): `from-path-monoid` takes the five
  STRUCTURE fields of a monoidal category (tensor, unit, three structural
  natural isos — naturality is the only genuinely categorical input) plus a
  `Coherent-path-monoid` (paths + descent + path-level triangle/pentagon,
  fields named as in `is-strict-monoidal`), and produces the assembled
  `Monoidal-category` together with `monoidal-is-strict`.  Mac Lane's
  triangle and pentagon are derived generically: `path→to-∙` (functoriality
  of path→iso), `ap-F₀-to-iso` at the bifunctor's `Right`/`Left`
  (whisker-commutation), `inv-is-path` (inverse legs descend), then
  `ap path-to` of the path-level axiom.  Structure fields pass through
  untouched, so the resulting components are definitionally the supplied
  ones.
- `Multicategory/Strictification.agda` (1369 → 1296): `Str-monoidal` and
  `Str-is-strict` are now `StrPM.monoidal/monoidal-is-strict` of
  `Str-path-monoid`.  DELETED: the hand-proved `.triangle` (~13 lines) and
  `.pentagon` (~32 lines) bodies, the `◀-≅`/`▶-≅` J-lemmas, `≅to-∘`, and the
  α←-direction `++-pentagon` with its sym-∙ derivation (that inversion now
  happens once, generically, inside the constructor).  The last hand-fought
  `ap-∙`/path-algebra blocks in the file are gone.
- Validation protocol as before: prototyped in scratch (constructor generic
  + Str instantiation with DEFINITIONAL-compatibility probes — all
  components refl-equal to the old ones, `α→ ≡ ≅to (ap ⊗₀ ++-assoc)` etc.),
  then integrated; Coherence.agda compiled UNCHANGED, confirming zero
  downstream definitional drift.  All roots green; scratch removed.
- Mathematical content now named: strict monoidal structure = coherent
  path-monoid on the object space acting naturally (predicate
  `is-strict-monoidal` = descent, constructor `from-path-monoid` = descent
  data suffices).  Also a further 1lab-upstreaming candidate.

## Follow-up (session 2 cont.): J-elimination pass

Replaced eight of the nine remaining direct uses of J with named,
content-revealing arguments; exactly ONE J survives, deliberately:

- `str-bridge` (Strictification) and `bridge` (Coherence): both are now
  `ap-F₀-to-iso` — "functors send path→isos to path→isos" — at the
  hom-identity functors `Reindex` and `Unwrap` respectively.  `Reindex`
  moved from Equivalence.agda to Strictification.agda (its natural home,
  next to Str); Equivalence and Coherence import it from there.
- `path→iso-sym` (Instances/Monoidal): `≅-path (sym (path→to-sym C p))` —
  isos agree when their .to legs do, and the leg fact is 1lab's.
- `≅to-∘ₘ`, `restrict₃-α` (Strictification): the interval-application idiom —
  a new `≅to-pathp` filler (one line via 1lab's `Hom-pathp-reflr`) composed
  under the interval; `restrict₃-α` finishes with `idₘr` at a concrete
  context (where the boundary is definitionally refl).
- `restrict-α` (Strictification): restrict the *deforming* iso — a
  `Hom-pathp-refll` filler from ≅to (ap ⊗₀ q) to the identity — under the
  interval; at the far end restricting the identity is the universal arrow
  (`restrict-id`), and `from-pathp⁻` reads off exactly the stated subst form.
- `idr-assoc-coh` (Strictification): revealed as homotopy-naturality of
  ++-idr (the homotopy `_++ [] ∼ id`), inverted and reassociated with
  1Lab.Path.Reasoning's ∙-swapl.
- `transp-decomp` + `subst-dom-cod` (Strictification): both are instances of
  ONE new generic lemma `transport₂-split` (a transport of a two-index
  family splits one index at a time, in either order — instantiated at Homₘ
  and its flip).  This is the single surviving J in the codebase, kept
  because "reduce to the definitional case" IS the content of that lemma.

All roots typecheck; net −44 lines.  Remaining J census: 1 (transport₂-split).
