open import 1Lab.Prelude hiding (id ; _∘_)
open import Data.List
open import Data.List.Properties

open import Multicategory.Free

module Multicategory.Free.Identity {o h} (G : Multigraph o h) where

open import Multicategory.Free.Kit G

-- The identity substitution law for the simple type theory: substituting a
-- variable into the slot marked by s gives back the original term, over the
-- structural path witnessed by the split (Shulman's M[y/x] = M).  This is
-- the left identity law of the syntactic multicategory.

private variable
  x z A B C : Ty
  Γ Δ Θ Ξ Ψ Ρ Λ Μ Κ : Ctx

-- The one-dimensional path algebra (square→∙ˡ, flip-cancel, θ-step,
-- θ-step₂, ap-∙-step, diag-∙) lives in Kit: the view's soundness fields are
-- squares whose moving edge is the p/q boundary path, and those combinators
-- convert them into equalities between composite boundary paths.

-- ==========================================================================
-- Cast eliminators: peel a cast off an endpoint of a Tm/Sp PathP, moving
-- the base path by an α (given directly, or in the c ∙ e ≡ d form the
-- θ-steps produce).  The ∙P composite is formed AFTER plugging the filler,
-- as per the transport discipline of Strictification.
-- ==========================================================================

private
  cast-step : ∀ {z Λ Μ Κ} (c : Λ ≡ Μ) {d : Λ ≡ Κ} {e : Μ ≡ Κ}
              {t : Tm Λ z} {u : Tm Κ z}
            → PathP (λ i → Tm (d i) z) t u
            → sym c ∙ d ≡ e
            → PathP (λ i → Tm (e i) z) (cast c t) u
  cast-step {z = z} c {d = d} {t = t} h α =
    tm-over α (_∙P_ {B = λ Ρ' → Tm Ρ' z} {p = sym c} {q = d}
      (symP (cast-filler c t)) h)

  sp-cast-step : ∀ {As : List (Multigraph.Ob G)} {Λ Μ Κ} (c : Λ ≡ Μ)
                 {d : Λ ≡ Κ} {e : Μ ≡ Κ}
                 {ts : Sp Λ As} {us : Sp Κ As}
               → PathP (λ i → Sp (d i) As) ts us
               → sym c ∙ d ≡ e
               → PathP (λ i → Sp (e i) As) (sp-cast c ts) us
  sp-cast-step {As = As} c {d = d} {ts = ts} h α =
    sp-over α (_∙P_ {B = λ Ρ' → Sp Ρ' As} {p = sym c} {q = d}
      (symP (sp-cast-filler c ts)) h)

  cast-out : ∀ {z Λ Μ Κ} (c : Λ ≡ Μ) {d : Λ ≡ Κ} {e : Μ ≡ Κ}
             {t : Tm Λ z} {u : Tm Κ z}
           → PathP (λ i → Tm (d i) z) t u
           → c ∙ e ≡ d
           → PathP (λ i → Tm (e i) z) (cast c t) u
  cast-out c h θ = cast-step c h (flip-cancel c θ)

  sp-cast-out : ∀ {As : List (Multigraph.Ob G)} {Λ Μ Κ} (c : Λ ≡ Μ)
                {d : Λ ≡ Κ} {e : Μ ≡ Κ}
                {ts : Sp Λ As} {us : Sp Κ As}
              → PathP (λ i → Sp (d i) As) ts us
              → c ∙ e ≡ d
              → PathP (λ i → Sp (e i) As) (sp-cast c ts) us
  sp-cast-out c h θ = sp-cast-step c h (flip-cancel c θ)

-- ==========================================================================
-- δ-lemmas: with the substituend context the singleton x ∷ [], each
-- reassociation helper composed with the split-path of the corresponding
-- weakened split is an ap of the original split-path.  All by structural
-- induction, the cons step being the same ap-∙ shuffle every time.
-- ==========================================================================

private
  δˡ : ∀ {x Θ Γ₁ Ξ₁} (s₁ : Split x Θ Γ₁ Ξ₁) (Κ' : Ctx)
     → flattenˡ Θ (x ∷ []) Ξ₁ Κ' ∙ split-path (split-++ˡ s₁ Κ')
     ≡ ap (_++ Κ') (split-path s₁)
  δˡ here Κ' = ∙-idl refl
  δˡ {x = x} {Θ = a ∷ Θ} (there s₁) Κ' =
    ap-∙-step (a ∷_)
      {p = flattenˡ Θ (x ∷ []) _ Κ'} {q = split-path (split-++ˡ s₁ Κ')}
      (δˡ s₁ Κ')

  δʳ : ∀ {x Θ Δ₁ Ξ} (Λ' : Ctx) (s₂ : Split x Θ Δ₁ Ξ)
     → flattenʳ Λ' Θ (x ∷ []) Ξ ∙ split-path (split-++ʳ Λ' s₂)
     ≡ ap (Λ' ++_) (split-path s₂)
  δʳ []       s₂ = ∙-idl _
  δʳ {x = x} {Θ = Θ} {Ξ = Ξ} (a ∷ Λ') s₂ =
    ap-∙-step (a ∷_)
      {p = flattenʳ Λ' Θ (x ∷ []) Ξ} {q = split-path (split-++ʳ Λ' s₂)}
      (δʳ Λ' s₂)

  δᵐ : ∀ {x Θ Ψ' Ξ₁} (Γm : Ctx) (s₁ : Split x Θ Ψ' Ξ₁) (Δm : Ctx)
     → flattenᵐ Γm Θ (x ∷ []) Ξ₁ Δm ∙ split-path (split-++ʳ Γm (split-++ˡ s₁ Δm))
     ≡ ap (λ Ψ'' → Γm ++ Ψ'' ++ Δm) (split-path s₁)
  δᵐ []       s₁ Δm = δˡ s₁ Δm
  δᵐ {x = x} {Θ = Θ} {Ξ₁ = Ξ₁} (a ∷ Γm) s₁ Δm =
    ap-∙-step (a ∷_)
      {p = flattenᵐ Γm Θ (x ∷ []) Ξ₁ Δm}
      {q = split-path (split-++ʳ Γm (split-++ˡ s₁ Δm))}
      (δᵐ Γm s₁ Δm)

  δ-bury-nil : ∀ {x Θ Δm Ξ} (Ψ' : Ctx) (s₂ : Split x Θ Δm Ξ)
             → sym (++-assoc Ψ' Θ (x ∷ Ξ)) ∙ split-path (split-++ʳ Ψ' s₂)
             ≡ ap (Ψ' ++_) (split-path s₂)
  δ-bury-nil []       s₂ = ∙-idl _
  δ-bury-nil {x = x} {Θ = Θ} {Ξ = Ξ} (a ∷ Ψ') s₂ =
    ap-∙-step (a ∷_)
      {p = sym (++-assoc Ψ' Θ (x ∷ Ξ))} {q = split-path (split-++ʳ Ψ' s₂)}
      (δ-bury-nil Ψ' s₂)

  δ-bury : ∀ {x Θ Δm Ξ} (Γm Ψ' : Ctx) (s₂ : Split x Θ Δm Ξ)
         → bury Γm Ψ' Θ (x ∷ Ξ) ∙ split-path (split-++ʳ Γm (split-++ʳ Ψ' s₂))
         ≡ ap (λ Δ' → Γm ++ Ψ' ++ Δ') (split-path s₂)
  δ-bury []       Ψ' s₂ = δ-bury-nil Ψ' s₂
  δ-bury {x = x} {Θ = Θ} {Ξ = Ξ} (a ∷ Γm) Ψ' s₂ =
    ap-∙-step (a ∷_)
      {p = bury Γm Ψ' Θ (x ∷ Ξ)}
      {q = split-path (split-++ʳ Γm (split-++ʳ Ψ' s₂))}
      (δ-bury Γm Ψ' s₂)

-- ==========================================================================
-- The identity substitution law, mutually with its spine analogue and one
-- handler-level lemma per branch handler of sub (matching the view, so each
-- handler clause reduces definitionally).  The ʳ-lemmas additionally thread
-- the outer view's soundness square.
-- ==========================================================================

sub-id : ∀ {x z Θ Ρ Ξ} (s : Split x Θ Ρ Ξ) (t : Tm Ρ z)
       → PathP (λ i → Tm (split-path s i) z) (sub s t var) t

sub-sp-id : ∀ {x Θ Ρ Ξ} {As : List (Multigraph.Ob G)}
            (s : Split x Θ Ρ Ξ) (ts : Sp Ρ As)
          → PathP (λ i → Sp (split-path s i) As) (sub-sp s ts var) ts

sub-pair-id : ∀ {x A B Θ Γ₁ Δ₁ Ξ} {s : Split x Θ (Γ₁ ++ Δ₁) Ξ}
              (v : Split-++ Γ₁ Δ₁ s) (P : Tm Γ₁ A) (Q : Tm Δ₁ B)
            → PathP (λ i → Tm (split-path s i) (A ⊗ B))
                    (sub-pair v P Q var) ⦅ P , Q ⦆

sub-cons-id : ∀ {x Θ Γ₁ Δ₁ Ξ} {A : Multigraph.Ob G} {As : List (Multigraph.Ob G)}
              {s : Split x Θ (Γ₁ ++ Δ₁) Ξ} (v : Split-++ Γ₁ Δ₁ s)
              (t : Tm Γ₁ (base A)) (ts : Sp Δ₁ As)
            → PathP (λ i → Sp (split-path s i) (A ∷ As))
                    (sub-cons v t ts var) (t ∷ ts)

sub-match⊗-idˡ : ∀ {x A B C Θ Γm Ψ Δm Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
                 (v : Split-++ Γm (Ψ ++ Δm) s)
                 (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
               → PathP (λ i → Tm (split-path s i) C)
                       (sub-match⊗ˡ v P Q var) (match⊗ {Γ = Γm} {Δ = Δm} P Q)

sub-match⊗-idʳ : ∀ {x A B C Θ₂ Ψ Δm Ξ Γm Θ} {s' : Split x Θ₂ (Ψ ++ Δm) Ξ}
                 (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
                 {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
                 (co : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ)
                             (split-++ʳ Γm s') s)
                 (P : Tm Ψ (A ⊗ B)) (Q : Tm (Γm ++ A ∷ B ∷ Δm) C)
               → PathP (λ i → Tm (split-path s i) C)
                       (sub-match⊗ʳ v q P Q var) (match⊗ {Γ = Γm} {Δ = Δm} P Q)

sub-match𝟙-idˡ : ∀ {x C Θ Γm Ψ Δm Ξ} {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
                 (v : Split-++ Γm (Ψ ++ Δm) s)
                 (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C)
               → PathP (λ i → Tm (split-path s i) C)
                       (sub-match𝟙ˡ v P Q var) (match𝟙 {Γ = Γm} {Δ = Δm} P Q)

sub-match𝟙-idʳ : ∀ {x C Θ₂ Ψ Δm Ξ Γm Θ} {s' : Split x Θ₂ (Ψ ++ Δm) Ξ}
                 (v : Split-++ Ψ Δm s') (q : Γm ++ Θ₂ ≡ Θ)
                 {s : Split x Θ (Γm ++ Ψ ++ Δm) Ξ}
                 (co : PathP (λ k → Split x (q k) (Γm ++ Ψ ++ Δm) Ξ)
                             (split-++ʳ Γm s') s)
                 (P : Tm Ψ 𝟙) (Q : Tm (Γm ++ Δm) C)
               → PathP (λ i → Tm (split-path s i) C)
                       (sub-match𝟙ʳ v q P Q var) (match𝟙 {Γ = Γm} {Δ = Δm} P Q)

-- The var case, standalone so that sub-id always matches the term first
-- (matching the split first strands coverage on Γ ++ Δ ≟ x ∷ Ξ, exactly as
-- for sub-var itself).
sub-var-id : ∀ {x z Θ Ξ} (s : Split x Θ (z ∷ []) Ξ)
           → PathP (λ i → Tm (split-path s i) z) (sub-var s var) var
sub-var-id here      = transport-refl var
sub-var-id (there s) = absurd (split-[] s)

sub-id s var = sub-var-id s
sub-id s (gen f ts) i = gen f (sub-sp-id s ts i)
sub-id s (⦅_,_⦆ {Γ = Γ₁} P Q)   = sub-pair-id (split-++ Γ₁ s) P Q
sub-id s (match⊗ {Γ = Γm} P Q) = sub-match⊗-idˡ (split-++ Γm s) P Q
sub-id s ⋆ = absurd (split-[] s)
sub-id s (match𝟙 {Γ = Γm} P Q) = sub-match𝟙-idˡ (split-++ Γm s) P Q

sub-sp-id s []                   = absurd (split-[] s)
sub-sp-id s (_∷_ {Γ = Γ₁} t ts)  = sub-cons-id (split-++ Γ₁ s) t ts

sub-pair-id {x = x} {Θ = Θ} {Δ₁ = Δ₁} (on-left {Ξ₁ = Ξ₁} s₁ p co) P Q =
  cast-out (flattenˡ Θ (x ∷ []) Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ x ∷ Ξ') p)
    (λ i → ⦅ sub-id s₁ P i , Q ⦆)
    (θ-step (flattenˡ Θ (x ∷ []) Ξ₁ Δ₁) (λ k → split-path (co k)) (δˡ s₁ Δ₁))

sub-pair-id {x = x} {Γ₁ = Γ₁} {Ξ = Ξ} (on-right {Θ₂ = Θ₂} s₂ q co) P Q =
  cast-out (flattenʳ Γ₁ Θ₂ (x ∷ []) Ξ ∙ ap (λ Θ' → Θ' ++ x ∷ Ξ) q)
    (λ i → ⦅ P , sub-id s₂ Q i ⦆)
    (θ-step (flattenʳ Γ₁ Θ₂ (x ∷ []) Ξ) (λ k → split-path (co k)) (δʳ Γ₁ s₂))

sub-cons-id {x = x} {Θ = Θ} {Δ₁ = Δ₁} (on-left {Ξ₁ = Ξ₁} s₁ p co) t ts =
  sp-cast-out (flattenˡ Θ (x ∷ []) Ξ₁ Δ₁ ∙ ap (λ Ξ' → Θ ++ x ∷ Ξ') p)
    (λ i → sub-id s₁ t i ∷ ts)
    (θ-step (flattenˡ Θ (x ∷ []) Ξ₁ Δ₁) (λ k → split-path (co k)) (δˡ s₁ Δ₁))

sub-cons-id {x = x} {Γ₁ = Γ₁} {Ξ = Ξ} (on-right {Θ₂ = Θ₂} s₂ q co) t ts =
  sp-cast-out (flattenʳ Γ₁ Θ₂ (x ∷ []) Ξ ∙ ap (λ Θ' → Θ' ++ x ∷ Ξ) q)
    (λ i → t ∷ sub-sp-id s₂ ts i)
    (θ-step (flattenʳ Γ₁ Θ₂ (x ∷ []) Ξ) (λ k → split-path (co k)) (δʳ Γ₁ s₂))

sub-match⊗-idˡ {x = x} {A = A} {B = B} {Θ = Θ} {Ψ = Ψ} {Δm = Δm}
  (on-left {Ξ₁ = Ξ₁} s₁ p co) P Q =
  cast-out (flattenˡ Θ (x ∷ []) Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ x ∷ Ξ') p)
    (λ i → match⊗ {Γ = split-path s₁ i} {Δ = Δm} P
             (cast-step (sym (flattenˡ Θ (x ∷ []) Ξ₁ (A ∷ B ∷ Δm)))
               (sub-id (split-++ˡ s₁ (A ∷ B ∷ Δm)) Q)
               (δˡ s₁ (A ∷ B ∷ Δm)) i))
    (θ-step (flattenˡ Θ (x ∷ []) Ξ₁ (Ψ ++ Δm)) (λ k → split-path (co k))
      (δˡ s₁ (Ψ ++ Δm)))

sub-match⊗-idˡ {Ψ = Ψ} (on-right s' q co) P Q =
  sub-match⊗-idʳ (split-++ Ψ s') q co P Q

sub-match⊗-idʳ {x = x} {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm}
  (on-left {Ξ₁ = Ξ₁} s₁ p co') q {s = s} co P Q =
  cast-out (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm ∙ (λ i → q i ++ x ∷ p i))
    (λ i → match⊗ {Γ = Γm} {Δ = Δm} (sub-id s₁ P i) Q)
    ( ap (λ w → (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm ∙ w) ∙ split-path s)
         (diag-∙ (λ Θ' Ξ' → Θ' ++ x ∷ Ξ') q p)
    ∙ θ-step₂ (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm)
        (λ k → split-path (co k))
        (λ k → split-path (split-++ʳ Γm (co' k)))
        (δᵐ Γm s₁ Δm))

sub-match⊗-idʳ {x = x} {A = A} {B = B} {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm}
  (on-right {Θ₂ = Θ₃} s₂ q₂ co') q {s = s} co P Q =
  cast-out (bury Γm Ψ Θ₃ (x ∷ Ξ) ∙ ap (λ Θ' → Θ' ++ x ∷ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (λ i → match⊗ {Γ = Γm} {Δ = split-path s₂ i} P
             (cast-step (sym (flattenʳ Γm (A ∷ B ∷ Θ₃) (x ∷ []) Ξ))
               (sub-id (split-++ʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) Q)
               (δʳ Γm (split-++ʳ (A ∷ B ∷ []) s₂)) i))
    ( ap (λ w → (bury Γm Ψ Θ₃ (x ∷ Ξ) ∙ w) ∙ split-path s)
         (ap-∙ (λ Θ' → Θ' ++ x ∷ Ξ) (ap (Γm ++_) q₂) q)
    ∙ θ-step₂ (bury Γm Ψ Θ₃ (x ∷ Ξ))
        (λ k → split-path (co k))
        (λ k → split-path (split-++ʳ Γm (co' k)))
        (δ-bury Γm Ψ s₂))

sub-match𝟙-idˡ {x = x} {Θ = Θ} {Ψ = Ψ} {Δm = Δm}
  (on-left {Ξ₁ = Ξ₁} s₁ p co) P Q =
  cast-out (flattenˡ Θ (x ∷ []) Ξ₁ (Ψ ++ Δm) ∙ ap (λ Ξ' → Θ ++ x ∷ Ξ') p)
    (λ i → match𝟙 {Γ = split-path s₁ i} {Δ = Δm} P
             (cast-step (sym (flattenˡ Θ (x ∷ []) Ξ₁ Δm))
               (sub-id (split-++ˡ s₁ Δm) Q)
               (δˡ s₁ Δm) i))
    (θ-step (flattenˡ Θ (x ∷ []) Ξ₁ (Ψ ++ Δm)) (λ k → split-path (co k))
      (δˡ s₁ (Ψ ++ Δm)))

sub-match𝟙-idˡ {Ψ = Ψ} (on-right s' q co) P Q =
  sub-match𝟙-idʳ (split-++ Ψ s') q co P Q

sub-match𝟙-idʳ {x = x} {Θ₂ = Θ₂} {Δm = Δm} {Γm = Γm}
  (on-left {Ξ₁ = Ξ₁} s₁ p co') q {s = s} co P Q =
  cast-out (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm ∙ (λ i → q i ++ x ∷ p i))
    (λ i → match𝟙 {Γ = Γm} {Δ = Δm} (sub-id s₁ P i) Q)
    ( ap (λ w → (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm ∙ w) ∙ split-path s)
         (diag-∙ (λ Θ' Ξ' → Θ' ++ x ∷ Ξ') q p)
    ∙ θ-step₂ (flattenᵐ Γm Θ₂ (x ∷ []) Ξ₁ Δm)
        (λ k → split-path (co k))
        (λ k → split-path (split-++ʳ Γm (co' k)))
        (δᵐ Γm s₁ Δm))

sub-match𝟙-idʳ {x = x} {Ψ = Ψ} {Ξ = Ξ} {Γm = Γm}
  (on-right {Θ₂ = Θ₃} s₂ q₂ co') q {s = s} co P Q =
  cast-out (bury Γm Ψ Θ₃ (x ∷ Ξ) ∙ ap (λ Θ' → Θ' ++ x ∷ Ξ) (ap (Γm ++_) q₂ ∙ q))
    (λ i → match𝟙 {Γ = Γm} {Δ = split-path s₂ i} P
             (cast-step (sym (flattenʳ Γm Θ₃ (x ∷ []) Ξ))
               (sub-id (split-++ʳ Γm s₂) Q)
               (δʳ Γm s₂) i))
    ( ap (λ w → (bury Γm Ψ Θ₃ (x ∷ Ξ) ∙ w) ∙ split-path s)
         (ap-∙ (λ Θ' → Θ' ++ x ∷ Ξ) (ap (Γm ++_) q₂) q)
    ∙ θ-step₂ (bury Γm Ψ Θ₃ (x ∷ Ξ))
        (λ k → split-path (co k))
        (λ k → split-path (split-++ʳ Γm (co' k)))
        (δ-bury Γm Ψ s₂))
