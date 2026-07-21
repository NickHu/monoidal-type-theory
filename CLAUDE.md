# monoidal-type-theory

Formalising multicategories in cubical Agda using the [1lab](https://github.com/the1lab/1lab) library.

## Build

```fish
agda <Module>.agda
```

Agda 2.9.0 with the `--cubical` flag (set in `monoidal-type-theory.agda-lib`). The 1lab checkout is at `../1lab` (symlinked as `./1lab` for browsing). The library depends on 1lab.

## Architecture

- **`Multicategory.agda`** — `Premulticategory` record. Contexts are `List Obₘ` (no Fin, no Vec). Composition is decomposition-based:
  ```
  _∘ₘ_ : Homₘ (Θ ++ x ∷ Ξ) z → Homₘ Γ x → Homₘ (Θ ++ Γ ++ Ξ) z
  ```
  Laws range over homogeneous `≡`s (`++-idr`, `++-assoc`) where possible; `idₘl` is definitional. The reassociation helpers (`slot-unbury`, `assocₘ-boundary`, `assocₘ-flatten`, `interchange-slot₀/₁/₂`, `interchange-flatten`, `interchangeₘ-boundary`) are **public** (exported) and defined by **structural recursion** (cons-by-cons), NOT by composing `++-assoc` with `∙` — this is critical so that `homₘ`/`⊗-context` reduce through them definitionally, and public so instances can characterise `path→iso (ap ⊗-context/homₘ <path>)` for the law transports.

- **`Multicategory/Instances.agda`** — Every category is trivially a multicategory (only singleton contexts inhabited). All 4 laws proven. Case splits expose the first two elements of each list part (to make `homₘ` reduce); unused cases are auto-discharged by Agda's coverage checker (arguments whose type reduces to `⊥`).

- **`Multicategory/Representable.agda`** — Representable multicategory of a monoidal category. `Homₘ Γ τ = Hom (⊗-context Γ) τ` where `⊗-context` is a plain fold (`[] → Unit; x ∷ Γ → x ⊗ ⊗-context Γ`). Composition is `f ∘ plug`.

## 1lab API patterns

Key imports (see `Representable.agda` lines 3–9):
```agda
open import Cat.Univalent using (path→iso; Hom-transport)
open import Cat.Functor.Naturality
open import Cat.Functor.Base as FB
open Cat.Base._=>_ public using (is-natural)
```

| What | How |
|------|-----|
| iso from an object path | `path→iso : A ≡ B → A ≅ B` |
| `path→iso refl ≡ id-iso` | `path→iso-refl = transport-refl _` (proven inline) |
| `path→iso (ap (x ⊗_) p) ≡ ▶.F-map-iso (path→iso p)` | `path→iso-ap-⊗ x p = ap-F₀-to-iso p` (via `open FB.F-iso (-⊗-.Right x)`) |
| transport in Hom-sets | `Hom-transport C p q h : transport (λ i → Hom (p i) (q i)) h ≡ path→iso q .to ∘ h ∘ path→iso p .from` |
| unitor naturality square | `unitor-l .Isoⁿ.from .is-natural x y f` (needs `Cat.Functor.Naturality` + `open Cat.Base._=>_`) |
| associator naturality | `associator .Isoⁿ.to .is-natural _ _ _` |
| monoidal triangle | `triangle-α→ : (A ▶ λ← _) ∘ α→ _ ≡ ρ← _ ◊ _` (field, available after `open Monoidal-category M`) |

Whiskering: `_▶_` (infix 35, rmap, tensor object on the left) and `_◀_` (infix 35, lmap, tensor object on the right). Both **looser** than `_∘_` (infixr 40), so parenthesise whiskered terms that are `∘` operands.

Iso composition: `∙Iso` is **left-to-right** (`a ∙Iso b` = a first, then b). `Iso⁻¹` inverts. `≅` fields: `.to`, `.from`, `.invr` (.from ∘ .to ≡ id), `.invl` (.to ∘ .from ≡ id).

Functor reasoning: `▶.F-∘ : ▶.F₁ (f ∘ g) ≡ ▶.F₁ f ∘ ▶.F₁ g`, `▶.F-id : ▶.F₁ id ≡ id`, `▶.F-map-iso : iso → iso`.

**bicat! caveat (learned the hard way):** `Cat.Bi.Solver.bicat! (Deloop M)` closes PURE associator/unitor coherences (pentagon, triangle) but **cannot** move a 2-cell whose domain/codomain are *stuck* `⊗-context …` terms (e.g. `φ Γ Δ = (⊗-context-++ Γ Δ).from : ⊗Γ⊗⊗Δ → ⊗(Γ++Δ)`) past an associator — its NbE leaves those objects unreconciled and `refl` on `nf₂` fails. For those naturality moves use the explicit 1lab lemmas: middle-slot `α→` naturality = `◀-▶-comm .Isoⁿ.to .is-natural` (functor `x ↦ (g▶x)◀f`, eta `α→(g,x,f)`); third-slot = `▶-assoc .Isoⁿ.to .is-natural` (functor `x ↦ (f⊗g)▶x` ≅ `f▶(g▶x)`, eta `α→(f,g,x)`). Both give clean `▶`/`◀` whiskering with no `id⊗id` noise. Pentagon: `pentagon-α→` (from `open Monoidal-category M`).

## Current state of Representable.agda

| Law | Status | Approach |
|------|--------|----------|
| `idₘl` | ✅ proven | `plug Θ [x] Ξ (ρ← x) ≡ id` via `triangle-α→` |
| `idₘr` | ✅ proven | Hom-transport over `++-idr` + the `core` chain (naturality squares + unit coherences) |
| `assocₘ` | ✅ proven | `g-free = gfi Θ` (prefix induction); base via `dec-nil`+`gfi0 Φ`; `gfi0 []` via `plug-nil`/`flat-from`/`-⊗-.rlmap`/`F-α→-to`/`◀-assoc`; all machinery in `dec-cons`/`plug-cons`/`plug-nil`/`F-α→-to` |
| `interchangeₘ` | ✅ proven | `ic-plug-coherence = ici Θ` (prefix induction, clean cons); base `ici []` via `plug-nil` + `ic-core` (g-free Γ-induction) + `-⊗-.rlmap` (g/h commute) |

**🎉 ALL FOUR LAWS PROVEN — `Multicategory/Representable.agda` type-checks with ZERO holes (2026-07-21).** The representable multicategory of a monoidal category is fully formalised.

**`F-α→` (strong-monoidal-functor hexagon) — ✅ PROVEN (2026-07-21).** `φ Γ Δ = (⊗-context-++ Γ Δ).from`; `F-α→ : ++-assoc-⊗-iso Γ Δ Ξ .to ∘ φ (Γ++Δ) Ξ ∘ (φ Γ Δ ◀ ⊗Ξ) ≡ φ Γ (Δ++Ξ) ∘ (⊗Γ ▶ φ Δ Ξ) ∘ α→(⊗Γ,⊗Δ,⊗Ξ)`. Base `[]` via `triangle-λ←` + unitor nat. Cons via **coh1** (`◀.F-∘` + `◀-▶-comm` + `▶.F-∘`) → `ap (a▶_) IH` → **coh2** (`▶.F-∘` + `pentagon-α→` + `▶-assoc`).

**`g-free` reduced to `gfi0 []` — ✅ mostly PROVEN (2026-07-21).** `g-free = gfi Θ` inducts on the prefix. Proven: reusable lemmas `dec-cons`, `plug-cons` (plug is prefix-linear: `plug (a∷Ω) = a ▶ plug Ω`), `dec-nil`, `plug-nil`, `flat-from`; `gfi` cons (dec-cons + plug-cons + `▶-assoc.from` push-out); `gfi []` (`dec-nil` + λ→-nat + `gfi0 Φ`); `gfi0` cons (pp-cons refl + plug-cons + `◀-▶-comm.from`). **Remaining: `gfi0 []`** — fully worked out on paper (closes): `plug-nil`/`flat-from`/pp-cons simplify, then `-⊗-.rlmap` (bifunctor interchange for h) + `F-α→-to` (the `.to`/ψ-mirror of the hexagon — prove by its own Ρ-induction or invert `F-α→`) + α→ first-slot nat + `α≅.invr` cancel + `◀.F-∘`. See memory `representable-law-proofs`.

### Key infrastructure added (all proven, type-check)

- `⊗-context-++-[]-ρ : (⊗-context-++ Γ []).to ∘ (⊗-context-++-idr Γ).from ≡ ρ→ (⊗-context Γ)` — cons-by-cons; base `idr _ ∙ λ→≡ρ→`, step `sym triangle-ρ→`.
- Monoidal coherence lemmas (`triangle-ρ←/→`, `triangle-λ←/→`, `λ←≡ρ←`, `λ→≡ρ→`) via `open Cat.Bi.Reasoning (Deloop M) using (...)` — import with `import Cat.Bi.Reasoning` (NOT `open import`; the parameterised module's `λ≅`/`ρ≅` clash with `Monoidal-category`'s).
- `path→iso` characterisations for the assocₘ transports (all cons-by-cons inductions via `path→iso-ap-⊗`, paralleling `⊗-context-++-idr-path`): `++-assoc-⊗-iso`/`-path`, `slot-unbury-iso`/`-⊗`, `assocₘ-flatten-iso`/`-⊗`, `assocₘ-boundary-iso`/`-⊗`. Each says `path→iso (ap ⊗-context <list-reassoc-path>)` is a `▶`-chain of `id-iso` (⊗-context is invariant under list reassociation).
- The list-reassoc helpers (`slot-unbury`, `assocₘ-boundary`, `assocₘ-flatten`, …) are now **public** in `Multicategory.agda` (were `private`) so these characterisations can name them.

### assocₘ assembly (the remaining piece)

`assocₘ f g h = to-pathp eq`. Via `Hom-transport`, the two transports become iso precomposition:
- `subst (λ Ω → Homₘ Ω z) (slot-unbury Θ Φ y Ψ Ξ) (f ∘ₘ g) = (f ∘ₘ g) ∘ slot-unbury-iso .from`
- `transport (λ i → Hom (⊗(assocₘ-boundary … i)) z) LHS = LHS ∘ assocₘ-boundary-iso .from`

So `eq` reduces to:
```
((f ∘ plug Θ (Φ++y∷Ψ) Ξ g) ∘ slot-unbury-iso .from) ∘ plug (Θ++Φ) Ρ (Ψ++Ξ) h ∘ assocₘ-boundary-iso .from
  ≡ f ∘ plug Θ (Φ++Ρ++Ψ) Ξ (g ∘ plug Φ Ρ Ψ h)
```
Unfold plugs (`splitL.from ∘ (⊗Θ ▶ (g ◊ ⊗Ξ)) ∘ splitR.to`) + the characterised isos (▶-chains + `⊗-context-++`), push f/g/h leftward with the naturality squares (`unitor-l/r .Isoⁿ.from .is-natural`), and the residual is the monoidal pentagon. `Cat.Bi.Solver.bicat! (Deloop M)` discharges pure associator/unitor coherences at the object level (confirmed: solves the pentagon); **caveat**: `import Cat.Bi.Solver` turns the `Mc .field = …` record implementations into `[MissingTypeSignature.Function]` errors — work around by giving those fields explicit `:` type signatures.

**Progress / findings on the assembly (2026-07):**
- `bicat! (Deloop M)` **does handle naturality** (morphism leaves interacting with associators/unitators) — confirmed: `bicat-nat : λ← b ∘ (Unit ▶ f) ≡ f ∘ λ← a` is `bicat! (Deloop M)`. BUT it works on term *syntax*, so it cannot see through `⊗-context-++ Θ Δ` / `plug` when Θ,Δ are **variables** (they are stuck). It only closes the coherence once lists are concrete.
- The assocₘ proof has been reduced (all VERIFIED, compiles) by successive cancellation:
  1. transport reduction (`transport-⊗-red`, `subst-red`) + `ap (f ∘_)` → **plug-coherence** `plugL ∘ slot-iso.from ∘ plugH ∘ bdry-iso.from ≡ plugR`;
  2. unfold plugs (`splitL.from ∘ (⊗Θ ▶ (g ◊ ⊗Ξ)) ∘ dec.to`) + `▶.F-∘`/`◀.F-∘` merge + `ap` → **g-free** `decL.to ∘ slot-iso.from ∘ plugH ∘ bdry-iso.from ≡ (⊗Θ ▶ (plugGH ◊ ⊗Ξ)) ∘ decR.to` (h only).
  This is the current hole (`g-free`). `plugL/plugH/plugR/plugGH`, `splitL/decL/decR`, `slot-iso/bdry-iso`, `merge-▶`, `transport-⊗-red`, `subst-red`, `eq` are all defined and checked.
- Remaining: `g-free` cancels `h` (plugH vs plugGH apply h at different groupings → an associator coherence), reaching a pure-iso coherence provable by list-induction; OR prove `g-free` directly by induction on Θ (h, plugGH are Θ-independent; base Θ=[] needs Φ-induction). This is the last hard piece of assocₘ.
- Induction on Θ is type-correct for the *f-free* coherence (g,h's types don't depend on Θ) but the Θ=[] base still has Φ,Ρ,Ψ variable and `⊗-context-++` stuck, so it needs further cancellation/induction.

### Gotchas (cost real time)

- 1lab `is-natural x y f : η y ∘ F.₁ f ≡ G.₁ f ∘ η x` (Cat.Base). The inline comments on `λ-nat-rho`/`ρ-nat-f` describe the REVERSE direction — verify against the convention and add `sym` as needed (idₘr's `core` uses `sym λ-nat-rho`, `sym ρ-nat-f`).
- `where` blocks here do NOT resolve forward references: a helper used in a clause must be TEXTUALLY BEFORE the clause.
- lmap whiskering is `_◀_` (U+25C0 BLACK LEFT-POINTING TRIANGLE), not `◊` (U+25CA). `_▶_` is rmap.
- `assoc f g h : f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h` (right→left regrouping); `sym assoc` for the reverse. `≅ .invr : from ∘ to ≡ id` (the `f ∘ id`-shaped one); `.invl : to ∘ from ≡ id`.

### Naming conventions

- Objects: `x y z` (z = codomain)
- Contexts: `Γ Δ Θ Ξ Φ Ψ Ρ Μ Κ`
- Morphisms: `f g h`
- `⊗-context` abbreviations: `split`, `φ`, `ψ` for local iso aliases
