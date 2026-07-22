module Scratch.A1 where

open import 1Lab.Prelude
open import Data.List using (List; []; _∷_; _++_; ++-idr; ++-assoc)

open import Multicategory

-- A1: the five J-proved transport-shuffling lemmas
--   Representable.∘ₘ-substr
--   Strictification.∘ₘ-substr / ∘ₘ-substl / ∘ₘ-substrG / ∘ₘ-subst-suf
-- are all instances of ONE lemma: _∘ₘ_ commutes with transporting the
-- prefix, suffix, and argument contexts simultaneously.  Moreover the
-- proof needs NO J at all: it is _∘ₘ_ applied under the interval
-- (an apd), read off with from-pathp.

module _ {o h} (M : Premulticategory o h) where
  open Premulticategory M

  ∘ₘ-subst : {Θ Θ' Ξ Ξ' Γ Γ' : List Obₘ} {x z : Obₘ}
             (p : Θ ≡ Θ') (q : Ξ ≡ Ξ') (r : Γ ≡ Γ')
             (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
           → _∘ₘ_ {Θ = Θ'} {Ξ = Ξ'}
               (transport (λ i → Homₘ (p i ++ x ∷ q i) z) f)
               (subst (λ Ω → Homₘ Ω x) r g)
             ≡ transport (λ i → Homₘ (p i ++ r i ++ q i) z)
                 (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-subst {x = x} {z = z} p q r f g = sym (from-pathp λ i →
    _∘ₘ_ {Θ = p i} {Ξ = q i}
      (transport-filler (λ j → Homₘ (p j ++ x ∷ q j) z) f i)
      (transport-filler (λ j → Homₘ (r j) x) g i))

  -- ── Instance 1: Representable.∘ₘ-substr and Strictification.∘ₘ-substr
  -- (they are verbatim identical).  Statement copied exactly.
  ∘ₘ-substr : {B B' : List Obₘ} {w z : Obₘ}
              (a : Homₘ (w ∷ []) z) (p : B ≡ B') (m : Homₘ B w)
            → _∘ₘ_ {Θ = []} {Ξ = []} a (subst (λ Ω → Homₘ Ω w) p m)
              ≡ subst (λ Ω → Homₘ ([] ++ Ω ++ []) z) p (_∘ₘ_ {Θ = []} {Ξ = []} a m)
  ∘ₘ-substr a p m =
    ap (λ k → _∘ₘ_ {Θ = []} {Ξ = []} k (subst _ p m)) (sym (transport-refl a))
    ∙ ∘ₘ-subst refl refl p a m

  -- ── Instance 2: Strictification.∘ₘ-substl.  Statement copied exactly.
  ∘ₘ-substl : {Θ Θ' Ξ Γ : List Obₘ} {x z : Obₘ}
              (p : Θ ≡ Θ') (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
            → _∘ₘ_ {Θ = Θ'} {Ξ = Ξ} (subst (λ Ω → Homₘ (Ω ++ x ∷ Ξ) z) p f) g
              ≡ subst (λ Ω → Homₘ (Ω ++ Γ ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-substl {Θ' = Θ'} {Ξ = Ξ} p f g =
    ap (_∘ₘ_ {Θ = Θ'} {Ξ = Ξ} (subst _ p f)) (sym (transport-refl g))
    ∙ ∘ₘ-subst p refl refl f g

  -- ── Instance 3: Strictification.∘ₘ-substrG.  Statement copied exactly.
  ∘ₘ-substrG : {Θ Ξ B B' : List Obₘ} {w z : Obₘ}
               (a : Homₘ (Θ ++ w ∷ Ξ) z) (p : B ≡ B') (m : Homₘ B w)
             → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} a (subst (λ Ω → Homₘ Ω w) p m)
               ≡ subst (λ Ω → Homₘ (Θ ++ Ω ++ Ξ) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} a m)
  ∘ₘ-substrG {Θ} {Ξ} a p m =
    ap (λ k → _∘ₘ_ {Θ = Θ} {Ξ = Ξ} k (subst _ p m)) (sym (transport-refl a))
    ∙ ∘ₘ-subst refl refl p a m

  -- ── Instance 4: Strictification.∘ₘ-subst-suf.  Statement copied exactly.
  ∘ₘ-subst-suf : {Θ Ξ Ξ' Γ : List Obₘ} {x z : Obₘ}
                 (p : Ξ ≡ Ξ') (f : Homₘ (Θ ++ x ∷ Ξ) z) (g : Homₘ Γ x)
               → _∘ₘ_ {Θ = Θ} {Ξ = Ξ'} (subst (λ Ω → Homₘ (Θ ++ x ∷ Ω) z) p f) g
                 ≡ subst (λ Ω → Homₘ (Θ ++ Γ ++ Ω) z) p (_∘ₘ_ {Θ = Θ} {Ξ = Ξ} f g)
  ∘ₘ-subst-suf {Θ} {Ξ' = Ξ'} p f g =
    ap (_∘ₘ_ {Θ = Θ} {Ξ = Ξ'} (subst _ p f)) (sym (transport-refl g))
    ∙ ∘ₘ-subst refl p refl f g
