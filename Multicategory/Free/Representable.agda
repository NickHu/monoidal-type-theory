open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties
open import Data.Set.Coequaliser

open import Multicategory.Free
import Multicategory.Representable as Rep

module Multicategory.Free.Representable {o h} (G : Multigraph o h) where

open import Multicategory.Free.SplitLemmas G
open import Multicategory.Free.Identity G
open import Multicategory.Free.Multicategory G

-- Representability of the syntactic multicategory (Theorem 2.4.10): the
-- n-ary tensor is the right-nested fold, its universal cone the nested
-- pairing of variables; universality of ⦅var,var⦆ and ⋆ is exactly β/η.

private variable
  x z A B : Ty
  Γ Δ Θ Ξ Λ : Ctx

-- The syntactic tensor of a context, and its universal cone.
⊗ᵗ : Ctx → Ty
⊗ᵗ []      = 𝟙
⊗ᵗ (A ∷ Γ) = A ⊗ ⊗ᵗ Γ

uᵗ : ∀ (Γ : Ctx) → Tm Γ (⊗ᵗ Γ)
uᵗ []      = ⋆
uᵗ (A ∷ Γ) = ⦅ var , uᵗ Γ ⦆

-- ==========================================================================
-- Split/path coherences for the section round-trips (all cons-by-cons).
-- ==========================================================================

-- The canonical split is the prefix-weakened `here`, over ++-idr.
split-here~ʳ : ∀ (Θ : Ctx) (x : Ty) (Ξ : Ctx)
             → PathP (λ i → Split x (++-idr Θ (~ i)) (Θ ++ x ∷ Ξ) Ξ)
                     (split-here Θ x Ξ) (split-++ʳ Θ here)
split-here~ʳ []      x Ξ = refl
split-here~ʳ (a ∷ Θ) x Ξ i = there (split-here~ʳ Θ x Ξ i)

-- The context path along which the section computation drifts.
idr⁻ : ∀ (Θ Λ : Ctx) → Θ ++ Λ ≡ (Θ ++ []) ++ Λ
idr⁻ Θ Λ i = ++-idr Θ (~ i) ++ Λ

-- flattenᵐ at the section's instances is exactly idr⁻.
flattenᵐ-idr𝟙 : ∀ (Θ Ξ : Ctx) → flattenᵐ Θ [] [] [] Ξ ≡ idr⁻ Θ Ξ
flattenᵐ-idr𝟙 []      Ξ = refl
flattenᵐ-idr𝟙 (a ∷ Θ) Ξ = ap (ap (a ∷_)) (flattenᵐ-idr𝟙 Θ Ξ)

flattenᵐ-idr⊗ : ∀ (Θ : Ctx) (A B : Ty) (Ξ : Ctx)
              → flattenᵐ Θ [] (A ∷ B ∷ []) [] Ξ ≡ idr⁻ Θ (A ∷ B ∷ Ξ)
flattenᵐ-idr⊗ []      A B Ξ = refl
flattenᵐ-idr⊗ (a ∷ Θ) A B Ξ = ap (ap (a ∷_)) (flattenᵐ-idr⊗ Θ A B Ξ)

-- β⊗'s boundary is the split-path of its outer identity substitution.
β⊗-sp : ∀ (Θ : Ctx) (A B : Ty) (Ξ : Ctx)
      → β⊗-boundary Θ (A ∷ []) (B ∷ []) Ξ
      ≡ split-path (split-++ʳ Θ (split-here (A ∷ []) B Ξ))
β⊗-sp []      A B Ξ = refl
β⊗-sp (a ∷ Θ) A B Ξ = ap (ap (a ∷_)) (β⊗-sp Θ A B Ξ)

-- ==========================================================================
-- Universality of ⋆ : the section round-trip at the Tm level.
-- ==========================================================================

sec𝟙 : ∀ {Θ Ξ : Ctx} {z : Ty} (N : Tm (Θ ++ Ξ) z)
     → sub (split-here Θ 𝟙 Ξ) (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Θ} {Δ = Ξ} var N) ⋆
     ≈ N
sec𝟙 {Θ} {Ξ} {z} N =
  ≈-trans (≈-sym (pathp→≈ {p = sym (idr⁻ Θ Ξ)} (symP S))) main
  where
    M𝟙 : Tm (Θ ++ (𝟙 ∷ []) ++ Ξ) z
    M𝟙 = match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Θ} {Δ = Ξ} var N

    S : PathP (λ i → Tm (idr⁻ Θ Ξ i) z)
          (sub (split-here Θ 𝟙 Ξ) M𝟙 ⋆)
          (sub (split-++ʳ Θ here) M𝟙 ⋆)
    S i = sub (split-here~ʳ Θ 𝟙 Ξ i) M𝟙 ⋆

    P∙ : Θ ++ Ξ ≡ (Θ ++ []) ++ Ξ
    P∙ = flattenᵐ Θ [] [] [] Ξ ∙ refl

    D : (Θ ++ []) ++ Ξ ≡ Θ ++ Ξ
    D = sym (idr⁻ Θ Ξ)

    E : sub (split-++ʳ Θ here) M𝟙 ⋆
      ≡ cast P∙ (match𝟙 {Ψ = []} {Γ = Θ} {Δ = Ξ} ⋆ N)
    E = ap (λ v → sub-match𝟙ˡ v var N ⋆) (split-++-ʳ Θ (here {Ξ = Ξ}))
      ∙ ap (λ t → cast P∙ (match𝟙 {Ψ = []} {Γ = Θ} {Δ = Ξ} t N))
           (transport-refl ⋆)

    main : cast D (sub (split-++ʳ Θ here) M𝟙 ⋆) ≈ N
    main =
      ≈-trans (≈-of-path (ap (cast D) E))
      (≈-trans (cast-≈ D (cast-≈ P∙ (β𝟙 {Γm = Θ} {Δm = Ξ} N)))
      (≈-trans (≈-of-path (ap (λ ρ → cast D (cast ρ N))
                 (∙-idr (flattenᵐ Θ [] [] [] Ξ) ∙ flattenᵐ-idr𝟙 Θ Ξ)))
        (pathp→≈ {p = D} (symP (cast-filler (idr⁻ Θ Ξ) N)))))

-- ⋆ is a universal arrow: plugging it in is inverted by match𝟙(var, -),
-- with the round trips exactly η𝟙 (+ sub-id) and β𝟙 (via sec𝟙).
𝟙-universal : Rep.is-universal FMonCat {Γ = []} {t = 𝟙} (inc ⋆)
𝟙-universal {Θ} {Ξ} {z} = is-iso→is-equiv isom
  where
    inv𝟙 : Homᶠ (Θ ++ [] ++ Ξ) z → Homᶠ (Θ ++ 𝟙 ∷ Ξ) z
    inv𝟙 = Coeq-rec
      (λ N → inc (match𝟙 {Ψ = 𝟙 ∷ []} {Γ = Θ} {Δ = Ξ} var N))
      (λ (a , b , r) → quot (match𝟙-cong {Γ = Θ} {Δ = Ξ} ≈-refl r))

    isom : is-iso (λ (f : Homᶠ (Θ ++ 𝟙 ∷ Ξ) z) → _∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f (inc ⋆))
    isom .is-iso.from = inv𝟙
    isom .is-iso.rinv = Coeq-elim-prop (λ n → squash _ n) λ N → quot (sec𝟙 {Θ = Θ} {Ξ = Ξ} N)
    isom .is-iso.linv = Coeq-elim-prop (λ f → squash _ f) λ F →
      quot (η𝟙 var F)
      ∙ incᵖ (tm-over (split-path-here Θ 𝟙 Ξ) (sub-id (split-here Θ 𝟙 Ξ) F))

-- ==========================================================================
-- Universality of ⦅var,var⦆ : the section round-trip at the Tm level.
-- ==========================================================================

sec⊗ : ∀ {A B : Ty} {Θ Ξ : Ctx} {z : Ty} (N : Tm (Θ ++ A ∷ B ∷ Ξ) z)
     → sub (split-here Θ (A ⊗ B) Ξ)
           (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Θ} {Δ = Ξ} var N) ⦅ var , var ⦆
     ≈ N
sec⊗ {A} {B} {Θ} {Ξ} {z} N =
  ≈-trans (≈-sym (pathp→≈ {p = sym (idr⁻ Θ (A ∷ B ∷ Ξ))} (symP S))) main
  where
    M⊗ : Tm (Θ ++ ((A ⊗ B) ∷ []) ++ Ξ) z
    M⊗ = match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Θ} {Δ = Ξ} var N

    S : PathP (λ i → Tm (idr⁻ Θ (A ∷ B ∷ Ξ) i) z)
          (sub (split-here Θ (A ⊗ B) Ξ) M⊗ ⦅ var , var ⦆)
          (sub (split-++ʳ Θ here) M⊗ ⦅ var , var ⦆)
    S i = sub (split-here~ʳ Θ (A ⊗ B) Ξ i) M⊗ ⦅ var , var ⦆

    P∙ : Θ ++ A ∷ B ∷ Ξ ≡ (Θ ++ []) ++ A ∷ B ∷ Ξ
    P∙ = flattenᵐ Θ [] (A ∷ B ∷ []) [] Ξ ∙ refl

    D : (Θ ++ []) ++ A ∷ B ∷ Ξ ≡ Θ ++ A ∷ B ∷ Ξ
    D = sym (idr⁻ Θ (A ∷ B ∷ Ξ))

    s₁ : Split A Θ (Θ ++ A ∷ B ∷ Ξ) (B ∷ Ξ)
    s₁ = split-here Θ A (B ∷ Ξ)

    s₂ : Split B (Θ ++ A ∷ []) (Θ ++ A ∷ B ∷ Ξ) Ξ
    s₂ = split-++ʳ Θ (split-here (A ∷ []) B Ξ)

    bd : (Θ ++ A ∷ []) ++ (B ∷ []) ++ Ξ ≡ Θ ++ (A ∷ B ∷ []) ++ Ξ
    bd = β⊗-boundary Θ (A ∷ []) (B ∷ []) Ξ

    E : sub (split-++ʳ Θ here) M⊗ ⦅ var , var ⦆
      ≡ cast P∙ (match⊗ {Ψ = A ∷ B ∷ []} {Γ = Θ} {Δ = Ξ} ⦅ var , var ⦆ N)
    E = ap (λ v → sub-match⊗ˡ v var N ⦅ var , var ⦆)
           (split-++-ʳ Θ (here {Ξ = Ξ}))
      ∙ ap (λ t → cast P∙ (match⊗ {Ψ = A ∷ B ∷ []} {Γ = Θ} {Δ = Ξ} t N))
           (transport-refl ⦅ var , var ⦆)

    q₁ : sub s₁ N var ≡ N
    q₁ = tm-over (split-path-here Θ A (B ∷ Ξ)) (sub-id s₁ N)

    main : cast D (sub (split-++ʳ Θ here) M⊗ ⦅ var , var ⦆) ≈ N
    main =
      ≈-trans (≈-of-path (ap (cast D) E))
      (≈-trans (cast-≈ D (cast-≈ P∙ (β⊗ {Γm = Θ} {Δm = Ξ} var var N)))
      (≈-trans (≈-of-path
                 (ap (λ t → cast D (cast P∙ (cast bd (sub s₂ t var)))) q₁))
      (≈-trans (≈-of-path
                 (ap (λ ρ → cast D (cast P∙ (cast ρ (sub s₂ N var))))
                     (β⊗-sp Θ A B Ξ)))
      (≈-trans (cast-≈ D (cast-≈ P∙ (pathp→≈ {p = split-path s₂} (sub-id s₂ N))))
      (≈-trans (≈-of-path (ap (λ ρ → cast D (cast ρ N))
                 (∙-idr (flattenᵐ Θ [] (A ∷ B ∷ []) [] Ξ)
                  ∙ flattenᵐ-idr⊗ Θ A B Ξ)))
        (pathp→≈ {p = D} (symP (cast-filler (idr⁻ Θ (A ∷ B ∷ Ξ)) N))))))))

-- ⦅var,var⦆ is a universal arrow: inverted by match⊗(var, -), round trips
-- exactly η⊗ (+ sub-id) and β⊗ (via sec⊗).
⊗-universal : ∀ {A B : Ty}
            → Rep.is-universal FMonCat {Γ = A ∷ B ∷ []} {t = A ⊗ B}
                (inc ⦅ var , var ⦆)
⊗-universal {A} {B} {Θ} {Ξ} {z} = is-iso→is-equiv isom
  where
    inv⊗ : Homᶠ (Θ ++ (A ∷ B ∷ []) ++ Ξ) z → Homᶠ (Θ ++ (A ⊗ B) ∷ Ξ) z
    inv⊗ = Coeq-rec
      (λ N → inc (match⊗ {Ψ = (A ⊗ B) ∷ []} {Γ = Θ} {Δ = Ξ} var N))
      (λ (a , b , r) → quot (match⊗-cong {Γ = Θ} {Δ = Ξ} ≈-refl r))

    isom : is-iso (λ (f : Homᶠ (Θ ++ (A ⊗ B) ∷ Ξ) z)
                   → _∘ᶠ_ {Θ = Θ} {Ξ = Ξ} f (inc ⦅ var , var ⦆))
    isom .is-iso.from = inv⊗
    isom .is-iso.rinv = Coeq-elim-prop (λ n → squash _ n)
      λ N → quot (sec⊗ {A = A} {B = B} {Θ = Θ} {Ξ = Ξ} N)
    isom .is-iso.linv = Coeq-elim-prop (λ f → squash _ f) λ F →
      quot (η⊗ var F)
      ∙ incᵖ (tm-over (split-path-here Θ (A ⊗ B) Ξ)
                      (sub-id (split-here Θ (A ⊗ B) Ξ) F))

-- ==========================================================================
-- Universality of the whole cone, by induction on the context: the cons
-- case is ⦅var,var⦆ ∘ᶠ uᵗ Γ (universal arrows compose), reconciled with
-- uᵗ (A ∷ Γ) over the ++-idr boundary.
-- ==========================================================================

u-universal : ∀ (Γ : Ctx)
            → Rep.is-universal FMonCat {Γ = Γ} {t = ⊗ᵗ Γ} (inc (uᵗ Γ))
u-universal [] = 𝟙-universal
u-universal (A ∷ Γ) =
  Rep.is-universal-over FMonCat {p = λ i → A ∷ ++-idr Γ i} conn
    (Rep.universal-∘ₘ FMonCat {Γ = Γ} {t = ⊗ᵗ Γ} {Θ = A ∷ []} {Ξ = []}
      (inc ⦅ var , var ⦆) (⊗-universal {A = A} {B = ⊗ᵗ Γ})
      (inc (uᵗ Γ)) (u-universal Γ))
  where
    X : Tm (A ∷ Γ ++ []) (A ⊗ ⊗ᵗ Γ)
    X = ⦅ var , cast (sym (++-idr Γ)) (uᵗ Γ) ⦆

    cleanup : cast (flattenʳ (A ∷ []) [] Γ [] ∙ refl) X ≡ X
    cleanup = ap (λ ρ → cast ρ X) (∙-idr (flattenʳ (A ∷ []) [] Γ []))
            ∙ transport-refl X

    pair-path : PathP (λ i → Tm (A ∷ ++-idr Γ i) (A ⊗ ⊗ᵗ Γ))
                  X ⦅ var , uᵗ Γ ⦆
    pair-path i = ⦅ var , symP (cast-filler (sym (++-idr Γ)) (uᵗ Γ)) i ⦆

    conn : PathP (λ i → Homᶠ (A ∷ ++-idr Γ i) (A ⊗ ⊗ᵗ Γ))
             (_∘ᶠ_ {Θ = A ∷ []} {Ξ = []} (inc ⦅ var , var ⦆) (inc (uᵗ Γ)))
             (inc (uᵗ (A ∷ Γ)))
    conn = incᵖ cleanup ◁ incᵖᵖ pair-path

-- The syntactic multicategory is representable (Theorem 2.4.10's tensor).
FMonCat-rep : Rep.is-representable FMonCat
FMonCat-rep Γ = ⊗ᵗ Γ , inc (uᵗ Γ) , u-universal Γ
