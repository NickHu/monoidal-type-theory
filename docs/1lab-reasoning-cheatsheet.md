# 1lab equational-reasoning cheat-sheet

A reference for the combinators available in 1lab for category-theoretic
equational reasoning. Compiled while analysing `Multicategory/Representable.agda`.
Everything here is already in the 1lab checkout at `../1lab`.

Learn the naming scheme once and most names become guessable:

- `pull*` fuses two arrows given `a ∘ b ≡ c`; `push*` is its `sym` (given `c ≡ a ∘ b`).
- suffix `l`/`r` = which end the "spare" morphism sticks out; `-inner` = rewrite lands in the middle of a longer chain; `3`/`4` = act on a 3-/4-fold composite.
- `elim*`/`intro*` remove/insert something equal to `id`; `cancel*`/`insert*` remove/insert an inverse **pair**.
- `intro*` = `sym elim*`, `push*` = `sym pull*`, `insert*` = `sym cancel*`.

## The one-stop entry point for monoidal proofs

```agda
open import Cat.Monoidal.Reasoning M   -- M : Monoidal-category C
```

This single open gives you, in one namespace (no clashes):

- **all of `Cat.Reasoning C`** (§1) — `pulll`, `extendl`, `cancell`, …
- **all of `Monoidal Cᵐ`** — `_⊗_`, `α→/α←`, `λ→/λ←`, `ρ→/ρ←`, `_▶_`, `_◀_`, `triangle`, `pentagon`, …
- the whiskering-associativity natural isos `▶-assoc`, `◀-assoc`, `◀-▶-comm`
- the **unitor/associator naturality squares** (see below)
- `module λ≅`, `module ρ≅`, `module α≅` (giving `.to/.from/.invl/.invr`)

### Naturality squares (replace raw `.Isoⁿ.{to,from}.is-natural _ _ f`)

```agda
λ→nat β : λ→ _ ∘ β        ≡ (id ▶ β) ∘ λ→ _
λ←nat β : λ← _ ∘ (id ▶ β) ≡ β ∘ λ← _
ρ→nat β : ρ→ _ ∘ β        ≡ (β ◀ id) ∘ ρ→ _
ρ←nat β : ρ← _ ∘ (β ◀ id) ≡ β ∘ ρ← _
```

`α→nat β γ δ` / `α←nat β γ δ` exist too but are stated with the 2-cell
horizontal composite `◆`, so for varying a *single* tensor factor use the
whiskering isos instead:

```agda
(▶-assoc {f = a} {g = b}) .Isoⁿ.to   .is-natural _ _ h  -- (a⊗b)▶h  ↔  a▶(b▶h)   via α→/α←
(◀-assoc {f = a} {g = b}) .Isoⁿ.from .is-natural _ _ h  -- (h◀a)◀b  ↔  h◀(a⊗b)
(◀-▶-comm {f = a}{g = b}) .Isoⁿ.to   .is-natural _ _ h  -- (b▶h)◀a  ↔  b▶(h◀a)
```

## 1. `Cat.Reasoning C` (plain-category reasoning)

Identity: `eliml/elimr/elim-inner` (delete an `id`), `introl/intror/intro-inner`
(insert), `id-comm`, `idl2/idr2`.

Reassociate-and-fuse — parametrised by `a ∘ b ≡ c`:

```
pulll : a ∘ (b ∘ f) ≡ c ∘ f          pullr : (f ∘ a) ∘ b ≡ f ∘ c
pull-inner : (f ∘ a) ∘ (b ∘ g) ≡ f ∘ c ∘ g
pulll3/pullr3/pulll4 …               pushl/pushr/push-inner (= sym, from c ≡ a∘b)
```

Squares — parametrised by `f ∘ h ≡ g ∘ i`:

```
extendl : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)   extendr : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i
extend-inner : a ∘ f ∘ h ∘ b ≡ a ∘ g ∘ i ∘ b        (+ 3/4 versions)
```

Batch reassoc:

```
centralize p q : f∘g∘h∘i ≡ a∘(b∘c)∘d     (rewrite both ends of a 4-chain)
centralizel/centralizer                   disperse/dispersel/disperser (inverse)
```

Cancellation — parametrised by `h ∘ i ≡ id`:

```
cancell : h ∘ (i ∘ f) ≡ f       cancelr : (f ∘ h) ∘ i ≡ f
cancel-inner : (f ∘ h) ∘ (i ∘ g) ≡ f ∘ g
deletel/deleter (drop a leading/trailing inverse pair)   insertl/insertr (= sym)
```

Swizzles (rewrite one side, cancel the other):

```
lswizzle : g ≡ h ∘ i → f ∘ h ≡ id → f ∘ g ≡ i
rswizzle : g ≡ i ∘ h → h ∘ f ≡ id → g ∘ f ≡ i
swizzle  : f∘g ≡ h∘i → g∘g' ≡ id → h'∘h ≡ id → h'∘f ≡ i∘g'
```

Congruence notation (nicer than `ap₂ _∘_` / nested `ap`):

```
p ⟩∘⟨ q   : f ∘ g ≡ h ∘ i        (rewrite both factors)
refl⟩∘⟨ q : f ∘ g ≡ f ∘ h        (rewrite right factor)
p ⟩∘⟨refl : f ∘ g ≡ h ∘ g        (rewrite left factor)
```

Invertibility lenses (move an invertible `f` across an equation — great for
"solve for the inverse" derivations):

```
pre-invr  : (a ∘ f.inv ≡ b) ≃ (a ≡ b ∘ f)      post-invr, pre-invl, post-invl
reassocl/reassocr : reassociate one side of an equation-as-goal
```

Iso gluing: `Iso-swapl/Iso-swapr` (flip a leg of a commuting iso-triangle),
`Iso-prism`, `≅-path`/`≅-path-from` (two isos equal if `.to`/`.from` agree),
`_∙Iso_` (reading-order compose), `_Iso⁻¹`, `make-iso`.

## 2. `Cat.Functor.Reasoning F` (image of a functor — open `module ▶ = … ` etc.)

For whiskering `▶`/`◀` these are all available as `▶.foo`, `◀.foo`:

```
▶.collapse (ab≡c) : F₁ a ∘ F₁ b ≡ F₁ c      -- merges two whiskers (= your sym (F-∘) uses)
▶.expand   (c≡ab) : F₁ c ≡ F₁ a ∘ F₁ b
▶.pulll/pullr : collapse + reassoc
▶.weave (a∘c≡b∘d) : F₁ a ∘ F₁ c ≡ F₁ b ∘ F₁ d   -- push a square through F
▶.extendl/extendr/extend-inner
▶.annihilate (a∘b≡id) : F₁ a ∘ F₁ b ≡ id        -- (you already use this)
▶.cancell/cancelr/cancel-inner
▶.⟨ p ⟩ = ap F₁ p
```

`◀.F-∘`/`▶.F-∘` also aliased in `Cat.Bi.Reasoning` as `◀-distribl`/`▶-distribr`.

## 3. General path tools

```
⌜ x ⌝            -- 1Lab.Reflection.Marker: focus marker
≡⟨ ap! p ⟩       -- macro: rewrite ONLY the ⌜…⌝-marked subterm of the previous line
≡˘⟨ ap¡ p ⟩      -- same, marking the next line, backwards proof
p ∙ q , sym p , _∙∙_∙∙_ , ap₂ , apd
x ≡⟨ p ⟩ q  /  x ≡˘⟨ p ⟩ q  (backwards)  /  x ≡⟨⟩ q  (definitional)  /  x ∎
```

`⌜_⌝ + ap!` is the biggest lever for shrinking deeply-nested `ap (λ z → …big context… z …) p` steps: mark the redex, forget the context.
