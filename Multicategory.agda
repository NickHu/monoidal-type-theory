open import 1Lab.Prelude hiding (map)
open import Data.Nat
open import Data.Fin.Base renaming (_<_ to _<ᶠ_)
open import Data.Fin.Extra
open import Data.Vec.Base hiding (_++_)
open import Data.Vec.Extra
open import Data.Vec.Splice

module Multicategory where

record Premulticategory (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    Obₘ : Type o
    Obₘ-is-set : is-set Obₘ
    Homₘ : {n : Nat} → Vec Obₘ n → Obₘ → Type h
    Homₘ-is-set : {n : Nat} {Γ : Vec Obₘ n} {τ : Obₘ} → is-set (Homₘ Γ τ)

    idₘ : ∀ {x} → Homₘ (x ∷ []) x
    _∘ₘ[_]_
      : ∀ {m n} {Δ : Vec Obₘ n} {Γ : Vec Obₘ m} {τ}
      → Homₘ Δ τ
      → (i : Fin n)
      → Homₘ Γ (lookup Δ i)
      → Homₘ (splice Δ i Γ) τ

    idₘl[_]_ : ∀ {n} {Γ : Vec Obₘ (suc n)} {τ} → (i : Fin (suc n)) → (f : Homₘ Γ τ) → PathP (λ j → Homₘ (splice-singleton-id {xs = Γ} {i = i} j) τ) (f ∘ₘ[ i ] idₘ) f
    idₘr : ∀ {n} {Γ : Vec Obₘ n} {τ} → (f : Homₘ Γ τ) → PathP (λ i → Homₘ (++-zeror {Γ = Γ} i) τ) (idₘ ∘ₘ[ fzero ] f) f

    assocₘ
      : ∀ {n m p} {Θ : Vec Obₘ (suc n)} {Δ : Vec Obₘ (suc m)} {Γ : Vec Obₘ p} {τ}
      → (i : Fin (suc n)) → (j : Fin (suc m))
      → (f : Homₘ Θ τ) → (g : Homₘ Δ (lookup Θ i)) → (h : Homₘ Γ (lookup Δ j))
      → PathP (λ t → Homₘ (splice-assoc Θ i Δ j Γ t) τ)
          ((f ∘ₘ[ i ] g) ∘ₘ[ j f+ i ]
            (subst (λ σ → Homₘ Γ σ) (sym (lookup-splice Θ i Δ j)) h))
          (f ∘ₘ[ i ] (g ∘ₘ[ j ] h))

    -- Interchange: plug into two distinct slots of f in either order.
    -- Axiom for i <ᶠ k; the k <ᶠ i case is derived in Reasoning.
    interchangeₘ
      : ∀ {n m p} {Θ : Vec Obₘ (suc (suc n))} {Γ : Vec Obₘ m} {Δ : Vec Obₘ p} {τ}
      → (i k : Fin (suc (suc n))) → (i<k : i <ᶠ k)
      → (f : Homₘ Θ τ)
      → (g : Homₘ Γ (lookup Θ i))
      → (h : Homₘ Δ (lookup Θ k))
      → PathP (λ t → Homₘ (splice-interchange Θ i k i<k Γ Δ t) τ)
          ((f ∘ₘ[ i ] g) ∘ₘ[ shift-spliceʳ {n = suc n} {m} {i} {k} i<k ]
            (subst (λ σ → Homₘ Δ σ) (sym (lookup-shiftʳ Θ i k i<k Γ)) h))
          ((f ∘ₘ[ k ] h) ∘ₘ[ shift-spliceˡ {n = suc n} {p} {i} {k} i<k ]
            (subst (λ σ → Homₘ Γ σ) (sym (lookup-shiftˡ Θ i k i<k Δ)) g))

module Reasoning {o h} (M : Premulticategory o h) where
  open Premulticategory M public

  -- Interchange with k <ᶠ i, by swapping the two slots in interchangeₘ.
  interchangeₘ-<
    : ∀ {n m p} {Θ : Vec Obₘ (suc (suc n))} {Γ : Vec Obₘ m} {Δ : Vec Obₘ p} {τ}
    → (i k : Fin (suc (suc n))) → (k<i : k <ᶠ i)
    → (f : Homₘ Θ τ)
    → (g : Homₘ Γ (lookup Θ i))
    → (h : Homₘ Δ (lookup Θ k))
    → PathP (λ t → Homₘ (splice-interchange-< Θ i k k<i Γ Δ t) τ)
        ((f ∘ₘ[ k ] h) ∘ₘ[ shift-spliceʳ {n = suc n} {p} {i = k} {k = i} k<i ]
          (subst (λ σ → Homₘ Γ σ) (sym (lookup-shiftʳ Θ k i k<i Δ)) g))
        ((f ∘ₘ[ i ] g) ∘ₘ[ shift-spliceˡ {n = suc n} {m} {i = k} {k = i} k<i ]
          (subst (λ σ → Homₘ Δ σ) (sym (lookup-shiftˡ Θ k i k<i Γ)) h))
  interchangeₘ-< i k k<i f g h = interchangeₘ k i k<i f h g
