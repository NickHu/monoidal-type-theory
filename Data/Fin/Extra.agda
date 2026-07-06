open import 1Lab.Prelude
open import Data.Nat
open import Data.Fin.Base renaming (_<_ to _<ᶠ_ ; _≤_ to _≤ᶠ_)

module Data.Fin.Extra where

_f+_ : ∀ {m n} (i : Fin (suc m)) (j : Fin (suc n)) → Fin (suc (m + n))
_f+_ {m} {n} (fin i ⦃ i≤m ⦄) (fin j ⦃ j≤n ⦄) =
  fin (i + j) ⦃ s≤s $ +-preserves-≤ i m j n (≤-peel i≤m) (≤-peel j≤n) ⦄

infixl 6 _f+_

f+-fzero
  : ∀ {m n} (j : Fin (suc m))
  → _f+_ {n = n} j fzero ≡ inject (s≤s (+-≤l m n)) j
f+-fzero j = fin-ap (+-zeror (j .lower))

f+-fsuc
  : ∀ {m n} (j : Fin (suc m)) (k : Fin (suc n))
  → PathP (λ t → Fin (suc (+-sucr m n t))) (j f+ fsuc k) (fsuc (j f+ k))
f+-fsuc j k = fin-ap (+-sucr (j .lower) (k .lower))

inject-fsuc
  : ∀ {m n} (j : Fin (suc m))
  → inject (s≤s (+-≤l (suc m) n)) (fsuc j)
      ≡ fsuc (inject (s≤s (+-≤l m n)) j)
inject-fsuc j = fin-ap refl

suc-pred : ∀ x → 1 ≤ x → suc (x - 1) ≡ x
suc-pred (suc x) _ = refl

fshift-lower : ∀ {n} (m : Nat) (k : Fin n) → fshift m k .lower ≡ m + k .lower
fshift-lower zero k = refl
fshift-lower (suc m) k = ap suc (fshift-lower m k)

-- Remap a later index k after replacing an earlier slot i with m elements.
-- Numerically: k ↦ k + m − 1.  (ʳ = the right/later index moves.)
shift-spliceʳ
  : ∀ {n m} {i k : Fin (suc n)} → i <ᶠ k → Fin (m + n)
shift-spliceʳ {n} {m} {i} {k} i<k =
  fin (m + k .lower - 1) ⦃ bound ⦄
  where
    1≤k : 1 ≤ k .lower
    1≤k = ≤-trans (s≤s 0≤x) i<k

    k≤n : k .lower ≤ n
    k≤n = ≤-peel (k .Fin.bounded)

    1≤m+k : 1 ≤ m + k .lower
    1≤m+k = ≤-trans 1≤k (+-≤r m (k .lower))

    bound : m + k .lower - 1 < m + n
    bound =
      ≤-trans
        (≤-refl' (suc-pred (m + k .lower) 1≤m+k))
        (+-preserves-≤l (k .lower) n m k≤n)

-- Remap an earlier index i after replacing a later slot k with p elements.
-- (The numerical index is unchanged; only the Fin bound grows.)
-- (ˡ = the left/earlier index is kept.)
shift-spliceˡ
  : ∀ {n p} {i k : Fin (suc n)} → i <ᶠ k → Fin (p + n)
shift-spliceˡ {n} {p} {i} {k} i<k =
  fin (i .lower) ⦃ ≤-trans (≤-trans i<k (≤-peel (k .Fin.bounded))) (+-≤r p n) ⦄

shift-spliceʳ-fzero
  : ∀ {n m} (k : Fin (suc n)) (i<k : fzero <ᶠ fsuc k)
  → shift-spliceʳ {n = suc n} {m} {i = fzero} {k = fsuc k} i<k ≡ fshift m k
shift-spliceʳ-fzero {n} {m} k i<k =
  fin-ap (ap (_- 1) (+-sucr m (k .lower)) ∙ sym (fshift-lower m k))

shift-spliceˡ-fzero
  : ∀ {n p} (k : Fin (suc n)) (i<k : fzero <ᶠ fsuc k)
  → PathP (λ t → Fin (+-sucr p n t))
      (shift-spliceˡ {n = suc n} {p} {i = fzero} {k = fsuc k} i<k)
      fzero
shift-spliceˡ-fzero _ _ = fin-ap refl

shift-spliceˡ-fsuc
  : ∀ {n p} {i k : Fin (suc n)} (i<k : fsuc i <ᶠ fsuc k)
  → PathP (λ t → Fin (+-sucr p n t))
      (shift-spliceˡ {n = suc n} {p} {i = fsuc i} {k = fsuc k} i<k)
      (fsuc (shift-spliceˡ {n = n} {p} {i} {k} (≤-peel i<k)))
shift-spliceˡ-fsuc _ = fin-ap refl

shift-spliceʳ-fsuc
  : ∀ {n m} {i k : Fin (suc n)} (i<k : fsuc i <ᶠ fsuc k)
  → PathP (λ t → Fin (+-sucr m n t))
      (shift-spliceʳ {n = suc n} {m} {i = fsuc i} {k = fsuc k} i<k)
      (fsuc (shift-spliceʳ {n = n} {m} {i} {k} (≤-peel i<k)))
shift-spliceʳ-fsuc {n} {m} {i} {k} i<k =
  fin-ap
    (ap (_- 1) (+-sucr m (k .lower))
     ∙ sym (suc-pred (m + k .lower)
         (≤-trans (≤-trans (s≤s 0≤x) (≤-peel i<k)) (+-≤r m (k .lower)))))
