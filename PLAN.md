2. Rewrite path through the dependencies

The dependency graph splits into two nearly independent halves meeting at Multicategory.agda + Representable.agda, joined again only at Free/Strict.agda. I'd do the coherence half first: it teaches the transport discipline on files a quarter the size of Interchange, and lands the headline theorem early. (If you care more about the type theory, phases C–D only need phase A, so you can swap B after C — except Free/Strict.agda, which needs Strictification.)

Phase A — core theory (~510 lines, warm-up).
1. Multicategory.agda (163) — the record; internalise why every boundary path is cons-by-cons and how ∘ₘ-subst works (operation under the interval, no J). Everything else is applications of this idea.
2. Multicategory/Unary.agda (35) — first taste of the stuck-transport-refl tax.
3. Multicategory/Instances/Category.agda (56) — degenerate instance; practice with laws splitting on list heads.
4. Multicategory/Representable.agda (212) — universality; the corepresentability bridge into 1lab.

Phase B — coherence theorem (~3140 lines).
5. Multicategory/Instances/Monoidal.agda (987) — hardest file of this half. Order within: ⊗-chain kit → plug + plug-cons/nil → the ▶-∘₄/cons-step shared cons machinery → F-α→ (the mathematical heart) → the four laws.
6. Monoidal/Strict.agda (272) — is-strict-monoidal, then from-path-monoid (pentagon/triangle derived from path-level coherence; a candidate to understand deeply and possibly upstream to 1lab).
7. Multicategory/Strictification.agda (1325) — learn the PathP kit (∘ₘ-pathp, hom-over, ic₂, the assoc₍|Θ||Φ|₎ family) before the proofs; splitμ's "one named PathP per algebraic move, ∙P at the end, one square" style is the house discipline at its best.
8. Multicategory/Strictification/Equivalence.agda (69).
9. Multicategory/Instances/Monoidal/Coherence.agda (488) — the μ-φ bridge, then monoidal-strictification. Checkpoint: headline theorem re-proved.

Phase C — syntax and the substitution laws (~8570 lines as written; the phase where your redesign pays off).
Before writing a line, decide on (a) the unified match constructor and sketch (b) the list-path coherence module — they determine every file here.
10. Multicategory/Free.agda (402) — syntax, Split, the Split-++ view, sub, _≈_. The best-written file in the Free half; study how sub avoids with so its branches are nameable.
11. Free/Kit.agda (161) + Free/SplitLemmas.agda (142) — the transport toolkit and split calculus; add your coherence module here.
12. Free/Identity.agda (289) — the easiest law; learn the dispatch/canonicalise/core pattern on it.
13. Free/CongruenceLeft.agda (134) — same pattern, cast-≈ instead of δ-lemmas.
14. Free/Assoc.agda (1706) — one-slot canonicalisation; the template for Interchange.
15. Free/Interchange.agda (4159 → target well under 2000 with the match unification) — the two-slot view Split²-++ is the one new idea; everything else you'll have seen in Assoc.
16. Free/RedexStability.agda (1231) — sits above Identity+Assoc+Interchange by necessity (β/η stability genuinely uses all three).
17. Free/CongruenceRight.agda (133) — induction on the ≈-derivation; β/η cases delegate to 16.
18. Free/Multicategory.agda (191) — the assembly; satisfying and short because 12–17 did the work.
19. Free/Representable.agda (233) — universality of ⦅var,var⦆/⋆ is β/η; the round-trips are the point.
20. Free/Strict.agda (32) — free strict monoidal category, via phase B.

Phase D — freeness (Thm 2.4.10, ~4710 lines as written).
21. Free/Eval.agda (158) — note the commitment that every reconciliation path is named; reconsider the prefix-generalised eval-sp here.
22. Free/Freeness.agda (3856) — the file with the most room for improvement; read Uniqueness first (out of order) to see the homogeneous alternative before committing to Freeness's heterogeneous style.
23. Free/Uniqueness.agda (694) — the Overᶠ/castₘ-inj packaged-base technique; short because it cancels bases pairwise.

Two practical notes. First, REVIEW.md (in the repo root — the branch's findings log F1–F29) is worth reading before phase A: it records not just the design but the refuted alternatives (e.g. why ⊗-chain must be a record, not a Σ), which is exactly what you need to avoid re-walking dead ends. Second, the gotchas section of CLAUDE.md (meta ambiguity around match𝟙, the ∀-binder annotation trap) reflects real typechecker behaviour in this codebase — those will bite during the rewrite regardless of how you restructure.
