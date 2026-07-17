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
  Laws range over homogeneous `≡`s (`++-idr`, `++-assoc`) where possible; `idₘl` is definitional. The reassociation helpers (`slot-unbury`, `assocₘ-boundary`, etc.) are **private** and defined by **structural recursion** (cons-by-cons), NOT by composing `++-assoc` with `∙` — this is critical so that `homₘ`/`⊗-context` reduce through them definitionally.

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

## Current state of Representable.agda

| Law | Status | Approach |
|------|--------|----------|
| `idₘl` | ✅ proven | `plug Θ [x] Ξ (ρ← x) ≡ id` via `triangle-α→` |
| `idₘr` | 🔧 transport + naturality done; core equation is a hole | See below |
| `assocₘ` | ⬜ hole | Pentagon |
| `interchangeₘ` | ⬜ hole | Bifunctoriality |

### idₘr core equation

The transport handling (Hom-transport + path→iso-refl + ⊗-context-++-idr-path) and naturality lemmas (`λ-nat-rho`, `ρ-nat-f`) are proven. The remaining hole is:

```
(ρ← z ∘ plug [] Γ [] f) ∘ (⊗-context-++-idr Γ) .from ≡ f
```

Proof chain (7 steps):
1. **λ-naturality**: `ρ←z ∘ λ←(z⊗Unit) = λ←z ∘ (Unit▶ρ←z)` — have `λ-nat-rho`
2. **▶.F-∘**: merge `(Unit▶ρ←z) ∘ (Unit▶(f◀Unit))` into `Unit▶(ρ←z ∘ (f◀Unit))`
3. **ρ-naturality**: `ρ←z ∘ (f◀Unit) = f ∘ ρ←(⊗Γ)` — have `ρ-nat-f`
4. **▶.F-∘**: merge `Unit▶(f ∘ ρ←⊗Γ)` into `(Unit▶f) ∘ (Unit▶ρ←⊗Γ)`
5. **Sub-lemma**: `(Unit▶ρ←⊗Γ) ∘ intro = λ→` where `intro = (⊗-context-++-++ [] Γ []).to ∘ (⊗-context-++-idr Γ).from`
6. **λ-naturality**: `λ←z ∘ (Unit▶f) = f ∘ λ←⊗Γ`
7. **λ←∘λ→ = id**: `λ≅ .invl`

Step 5 needs a coherence `ρ←(A⊗B) ∘ α←(A,B,Unit) = A ▶ ρ←B`, derivable from the triangle identity. This is the main remaining sub-goal.

### Naming conventions

- Objects: `x y z` (z = codomain)
- Contexts: `Γ Δ Θ Ξ Φ Ψ Ρ Μ Κ`
- Morphisms: `f g h`
- `⊗-context` abbreviations: `split`, `φ`, `ψ` for local iso aliases
