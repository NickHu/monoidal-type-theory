# monoidal-type-theory

Multicategories in cubical Agda over the [1lab](https://github.com/the1lab/1lab)
library, culminating in the coherence theorem: **every monoidal category is
monoidally equivalent to a strict one** (`monoidal-strictification` in
`Multicategory/Instances/Monoidal/Coherence.agda`).

## Build

```fish
agda <Module>.agda
```

Agda 2.9.0 with `--cubical` (flags in `monoidal-type-theory.agda-lib`).  The
1lab checkout is at `../1lab` (symlinked as `./1lab` for browsing).  Root
modules (checking these covers everything):
`Multicategory/Instances/Monoidal/Coherence.agda`,
`Multicategory/Strictification/Equivalence.agda`,
`Multicategory/Instances/Category.agda`.

A full review/refactor pass was performed on the `refactor` branch —
`REVIEW.md` there has the findings log and rationale for the current design.

## Architecture

```
Multicategory.agda                 Premulticategory record; list-reassociation
                                   paths (structural, cons-by-cons); the shared
                                   transport lemma ∘ₘ-subst (no J: _∘ₘ_ under
                                   the interval) and spine lemma ++-assoc-nil
Multicategory/Unary.agda           underlying category; is-multicategory
                                   (univalence of Unary M)
Multicategory/Representable.agda   universal arrows; Homₘ Γ - as a functor
                                   (F-∘ = plug-nat); a universal arrow
                                   corepresents it, so uniqueness of
                                   representations comes from 1lab's
                                   Cat.Functor.Hom.Representable
Multicategory/Instances/Category.agda   every category is a multicategory
Multicategory/Instances/Monoidal.agda   the representable multicategory Mc of a
                                   monoidal category: Homₘ Γ τ = Hom (⊗-context Γ) τ,
                                   composition f ∘ plug; all four laws
Multicategory/Strictification.agda abstract Hermida construction: strict
                                   monoidal category Str from any representable
                                   multicategory, + Str-is-strict
Multicategory/Strictification/Equivalence.agda   Reindex : Str ≃ Unary M
Multicategory/Instances/Monoidal/Coherence.agda  Comparison = Unwrap F∘ Reindex
                                   : Str → C is a strong monoidal equivalence;
                                   ends with monoidal-strictification
Multicategory/Free.agda            Shulman's simple type theory for monoidal
                                   categories (catlog Fig. 2.2) over a
                                   Multigraph: intrinsic Tm/Sp syntax, the
                                   structural Split slot witness, capture-free
                                   substitution sub (= Fig. 2.3), β/η
                                   congruence _≈_, quotient hom-sets.  Laws +
                                   representability are roadmap; see
                                   docs/shulman-stt.md
Monoidal/Strict.agda               is-strict-monoidal: tensor descends from a
                                   coherent path-monoid on the object type
                                   (path-level pentagon/triangle; free when Ob
                                   is a set); and its converse constructor
                                   from-path-monoid: structure fields + a
                                   coherent path-monoid ⇒ Monoidal-category
                                   with triangle/pentagon derived generically
                                   (+ strictness witness).  Str-monoidal is
                                   built this way.
```

Design invariants worth knowing before editing:

- **Contexts are `List Obₘ`** (no Fin/Vec).  Composition is decomposition-based:
  `_∘ₘ_ : Homₘ (Θ ++ x ∷ Ξ) z → Homₘ Γ x → Homₘ (Θ ++ Γ ++ Ξ) z`.
- The list-reassociation helpers in `Multicategory.agda` are **structural
  recursions** (cons-by-cons), never `∙`-composites — folds like `⊗-context`
  reduce through them definitionally, which is what makes the law transports
  tractable.  Three of them are definitional aliases of 1lab's `++-assoc`
  (itself cons-by-cons).  Keep it that way: a `∙`-composed path is an hcomp
  that folds cannot see through.
- **Instances/Monoidal**: `⊗-chain p` bundles the ▶-chain iso of a boundary
  path with its `path→iso` characterisation; the combinators
  `chain-refl/chain-∷/chain-sym` generate every law-boundary characterisation.
  The four prefix inductions share their cons case via `▶-∘₄`/`cons-step`/
  `▶-weave₄` (distribute the whisker, apply the IH, one naturality square).
  The PathP laws are discharged with `Cat.Univalent.Hom-pathp-refll`.
- **Strictification**: transport-heavy proofs stay in PathP land via the kit
  `∘ₘ-pathp` (heterogeneous congruence — `_∘ₘ_` applied under the interval),
  `hom-over`, `ic₂` (binary interchange with all transport junk absorbed
  once), and the `assoc₍|Θ||Φ|₎` wrapper family.  Rule: plug arrows into a
  PathP segment BEFORE `∙P`-composing segments (a `∙`-composite base path is
  not cons-headed, so `∘ₘ-pathp` cannot expose the slot afterwards).
- Nothing anywhere assumes `Obₘ` (or C's objects) form a set.

## 1lab API patterns

See `docs/1lab-reasoning-cheatsheet.md` for the full combinator reference.
High-value specifics for this codebase:

| What | How |
|------|-----|
| discharge `PathP (λ i → Hom (p i) B) f g` | `Hom-pathp-refll C : f ∘ path→iso p .from ≡ g → …` (Cat.Univalent) |
| `path→iso (ap (x ⊗_) p) ≡ ▶.F-map-iso (path→iso p)` | `ap-F₀-to-iso` via `open FB.F-iso (-⊗-.Right x)` |
| monoidal coherence lemmas (`triangle-ρ→`, `λ→≡ρ→`, `triangle-inv`, …) | `import Cat.Bi.Reasoning` then `open Cat.Bi.Reasoning (Deloop M) using (…)` — NOT `open import` (its `λ≅`/`ρ≅` clash with `Monoidal-category`'s); `Cat.Monoidal.Reasoning` does **not** re-export these |
| unitor/associator naturality | `λ→nat/λ←nat/ρ→nat/ρ←nat` and `▶-assoc/◀-assoc/◀-▶-comm .Isoⁿ.to .is-natural` (Cat.Monoidal.Reasoning / Cat.Bi.Reasoning) |
| invert a whole equation between composites | `swizzle` (Cat.Reasoning) — see `F-α→-to` |
| whisker-functor algebra | `▶`/`◀` are full `Cat.Functor.Reasoning` modules: `▶.annihilate`, `▶.pulll`, `▶.cancell`, `▶.collapse`, `▶.weave`, `-⊗-.rlmap`, … |

**bicat! caveat:** `Cat.Bi.Solver.bicat! (Deloop M)` closes pure
associator/unitor coherences but cannot move 2-cells whose endpoints are stuck
`⊗-context Γ` terms (variable Γ) — use the explicit naturality lemmas above.
It also breaks record-field type inference when imported (fields need explicit
signatures), which is why no file imports it.

## Gotchas (cost real time)

- 1lab `is-natural x y f : η y ∘ F.₁ f ≡ G.₁ f ∘ η x` (Cat.Base) — check the
  direction, add `sym` as needed.
- `where`-block helpers must be TEXTUALLY BEFORE the clause that uses them.
- lmap whiskering is `_◀_` (U+25C0), rmap is `_▶_`; both bind looser than `_∘_`.
- `assoc f g h : f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h`; `≅ .invr : from ∘ to ≡ id`,
  `.invl : to ∘ from ≡ id`.
- `∙Iso` composes left-to-right.
- Agda 2.9 requires a type signature on any definition with arguments on the
  LHS (`[MissingTypeSignature.Function]`).
- An `ap₂` whose lambda projects `.from`/`.to` from an iso-typed binder often
  leaves unsolved metas — use two sequential `ap`s (each pinning the other
  position) or annotate the binder types.
- An unannotated `∀`-binder whose type is constrained only through `_++_`/`≡`
  (e.g. `∀ Θ Γ → (Θ ++ Γ) ++ Δ ≡ …`) gets a fresh type meta that freezes
  unsolved; later *uses* of the lemma then fail with reflexive-looking
  constraints `X = X : List Ty (blocked on _N)` reported far from the
  culprit.  Annotate: `∀ (Θ Γ : Ctx) → …`.
- Named implicit arguments in clause LHS patterns (and constructor implicits
  in patterns) must respect the order of first appearance in the signature /
  constructor type — out-of-order named bindings give `[WrongHidingInLHS]`.
- Around context-indexed syntax (Multicategory/Free*): pass cast/transport
  paths EXPLICITLY (a path meta under `transp` blocks the unifier); pin
  congruence endpoints (`≈-refl {t = P}`) and `match𝟙`'s `{Γ = …} {Δ = …}`
  (its `Γ ++ Δ` index has no cons anchor); `∙-idr refl`-style arguments under
  `ap` need pinning too — and such constraints can go ambiguous
  *retroactively* as a file grows.

## Naming conventions

- Objects: `x y z` (z = codomain); contexts: `Γ Δ Θ Ξ Φ Ψ Ρ Μ Κ`;
  morphisms: `f g h`.
- `φ Γ Δ = (⊗-context-++ Γ Δ).from` is the strong-monoidal comparison map of
  `⊗-context`; `μ Γ Δ` is its Str-level analogue (bridged by `μ-φ`).
