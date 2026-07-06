open import 1Lab.Prelude hiding (map)
open import Data.Nat
open import Data.Fin.Base renaming (_<_ to _<ᶠ_ ; _≤_ to _≤ᶠ_)
open import Data.Fin.Extra
open import Data.Vec.Base hiding (_++_)
open import Data.Vec.Properties
open import Data.Vec.Extra

module Data.Vec.Splice where

-- Convention: xs, i — outer vector and index (length n ≥ 1 when Fin n is used);
--             ys, j — inserted / middle vector and index (length m or suc m);
--             zs    — innermost replacement (length p).

-- splice xs i ys replaces xs !! i with ys.
-- Result length m + (n - 1): remove one slot, add m.
splice : ∀ {ℓ} {A : Type ℓ} {n m : Nat}
  → Vec A n → (i : Fin n) → Vec A m → Vec A (m + (n - 1))
splice xs i ys with fin-view i
splice (x ∷ xs) _ ys | zero = ys ++ xs
splice {A = A} {n = suc zero} {m} (x ∷ xs) _ ys | suc j = absurd (Fin-absurd j)
splice {A = A} {n = suc (suc n)} {m} (x ∷ xs) _ ys | suc j =
  subst (Vec A) (sym (+-sucr m n)) (x ∷ splice xs j ys)

splice-singleton-id
  : ∀ {ℓ} {A : Type ℓ} {n : Nat} {xs : Vec A (suc n)} {i}
  → splice xs i (lookup xs i ∷ []) ≡ xs
splice-singleton-id {xs = x ∷ xs} {i} with fin-view i
... | zero = refl
splice-singleton-id {A = A} {n = suc n} {xs = x ∷ xs} {i} | suc j =
  subst (Vec A) (sym (+-sucr 1 n)) (x ∷ splice xs j (lookup xs j ∷ []))
    ≡⟨ is-set→subst-refl (Vec A) Nat-is-set (sym (+-sucr 1 n)) (x ∷ splice xs j (lookup xs j ∷ [])) ⟩
  x ∷ splice xs j (lookup xs j ∷ [])
    ≡⟨ Vec-path refl (splice-singleton-id {n = n} {xs = xs} {i = j}) ⟩
  x ∷ xs ∎

-- splice (x ∷ xs) (fsuc i) ys ≡ x ∷ splice xs i ys
-- (PathP along +-sucr; cancels the length-subst in splice's suc-clause)
splice-cons-fsuc
  : ∀ {ℓ} {A : Type ℓ} {n m}
  → (x : A) (xs : Vec A (suc n)) (i : Fin (suc n)) (ys : Vec A m)
  → PathP (λ t → Vec A (+-sucr m n t))
      (splice (x ∷ xs) (fsuc i) ys)
      (x ∷ splice xs i ys)
splice-cons-fsuc {A = A} {n} {m} x xs i ys =
  symP (transport-filler (ap (Vec A) (sym (+-sucr m n))) (x ∷ splice xs i ys))

lookup-pathp
  : ∀ {ℓ} {A : Type ℓ} {n : I → Nat}
  → {xs : Vec A (n i0)} {ys : Vec A (n i1)}
  → {i : Fin (n i0)} {j : Fin (n i1)}
  → PathP (λ t → Vec A (n t)) xs ys
  → PathP (λ t → Fin (n t)) i j
  → lookup xs i ≡ lookup ys j
lookup-pathp p q t = lookup (p t) (q t)

-- Looking up at j f+ i in splice xs i ys recovers lookup ys j
lookup-splice
  : ∀ {ℓ} {A : Type ℓ} {n m}
  → (xs : Vec A (suc n)) (i : Fin (suc n)) (ys : Vec A (suc m)) (j : Fin (suc m))
  → lookup (splice xs i ys) (j f+ i) ≡ lookup ys j
lookup-splice xs i ys j with fin-view i
lookup-splice (x ∷ xs) i ys j | zero =
  lookup (ys ++ xs) (j f+ fzero)
    ≡⟨ ap (lookup (ys ++ xs)) (f+-fzero j) ⟩
  lookup (ys ++ xs) (inject (s≤s (+-≤l _ _)) j)
    ≡⟨ lookup-++ˡ ys xs j ⟩
  lookup ys j ∎
lookup-splice {n = suc n} (x ∷ xs) i ys j | suc k =
  lookup (splice (x ∷ xs) (fsuc k) ys) (j f+ fsuc k)
    ≡⟨ lookup-pathp (splice-cons-fsuc x xs k ys) (f+-fsuc j k) ⟩
  lookup (splice xs k ys) (j f+ k)
    ≡⟨ lookup-splice xs k ys j ⟩
  lookup ys j ∎

-- Splicing into the left summand of ++:
--   splice (xs ++ ys) (inject i) zs ≡ splice xs i zs ++ ys
splice-++ˡ
  : ∀ {ℓ} {A : Type ℓ} {m n p}
  → (xs : Vec A (suc m)) (ys : Vec A n) (i : Fin (suc m)) (zs : Vec A p)
  → PathP (λ t → Vec A (+-associative p m n t))
      (splice (xs ++ ys) (inject (s≤s (+-≤l m n)) i) zs)
      (splice xs i zs ++ ys)
splice-++ˡ {A = A} {m} {n} {p} (x ∷ xs) ys i zs with fin-view i
... | zero = ++-associative zs xs ys
splice-++ˡ {A = A} {m = suc m} {n} {p} (x ∷ xs) ys i zs | suc j =
  beginᵥ[]
    splice ((x ∷ xs) ++ ys) (inject (s≤s (+-≤l (suc m) n)) (fsuc j)) zs
      ≡ᵥ⟨ ap (λ k → splice ((x ∷ xs) ++ ys) k zs) (inject-fsuc {n = n} j) ⟩
    splice ((x ∷ xs) ++ ys) (fsuc (inject (s≤s (+-≤l m n)) j)) zs
      ≡ᵥ[]⟨ splice-cons-fsuc x (xs ++ ys) (inject (s≤s (+-≤l m n)) j) zs ⟩
    x ∷ splice (xs ++ ys) (inject (s≤s (+-≤l m n)) j) zs
      ≡ᵥ[]⟨ (λ t → x ∷ splice-++ˡ xs ys j zs t) ⟩
    x ∷ (splice xs j zs ++ ys)
      ≡ᵥ[]˘⟨ ++-congˡ (splice-cons-fsuc x xs j zs) ys ⟩
    splice (x ∷ xs) (fsuc j) zs ++ ys ∎ᵥ

splice-assoc
  : ∀ {ℓ} {A : Type ℓ} {n m p}
  → (xs : Vec A (suc n)) (i : Fin (suc n)) (ys : Vec A (suc m)) (j : Fin (suc m)) (zs : Vec A p)
  → PathP (λ t → Vec A (+-associative p m n t))
      (splice (splice xs i ys) (j f+ i) zs)
      (splice xs i (splice ys j zs))
splice-assoc xs i ys j zs with fin-view i
splice-assoc {A = A} {n} {m} {p} (x ∷ xs) fzero ys j zs | zero =
  beginᵥ[]
    splice (ys ++ xs) (j f+ fzero) zs
      ≡ᵥ⟨ ap (λ k → splice (ys ++ xs) k zs) (f+-fzero j) ⟩
    splice (ys ++ xs) (inject (s≤s (+-≤l m n)) j) zs
      ≡ᵥ[]⟨ splice-++ˡ ys xs j zs ⟩
    splice ys j zs ++ xs ∎ᵥ
splice-assoc {A = A} {n = suc n} {m} {p} (x ∷ xs) i ys j zs | suc iₛ =
  beginᵥ[]
    splice (subst (Vec A) (sym (+-sucr (suc m) n)) (x ∷ splice xs iₛ ys)) (j f+ fsuc iₛ) zs
      ≡ᵥ[]⟨ (λ t → splice
        (symP (transport-filler (ap (Vec A) (sym (ap suc (+-sucr m n)))) (x ∷ splice xs iₛ ys)) t)
        (f+-fsuc j iₛ t) zs) ⟩
    splice (x ∷ splice xs iₛ ys) (fsuc (j f+ iₛ)) zs
      ≡ᵥ[]⟨ splice-cons-fsuc x (splice xs iₛ ys) (j f+ iₛ) zs ⟩
    x ∷ splice (splice xs iₛ ys) (j f+ iₛ) zs
      ≡ᵥ[]⟨ (λ t → x ∷ splice-assoc xs iₛ ys j zs t) ⟩
    x ∷ splice xs iₛ (splice ys j zs)
      ≡ᵥ[]˘⟨ splice-cons-fsuc x xs iₛ (splice ys j zs) ⟩
    splice (x ∷ xs) (fsuc iₛ) (splice ys j zs) ∎ᵥ

-- Length after splicing into the right summand of ++.
++ʳ-length : ∀ p m n → p + ((m + suc n) - 1) ≡ m + (p + n)
++ʳ-length p m n =
  ap (p +_) (ap (_- 1) (+-sucr m n))
  ∙ +-associative p m n ∙ ap (_+ n) (+-commutative p m) ∙ sym (+-associative m p n)

-- Length of a double splice into a length-(suc (suc n)) vector.
double-splice-length : ∀ p m n → p + ((m + suc n) - 1) ≡ m + ((p + suc n) - 1)
double-splice-length p m n =
  ++ʳ-length p m n ∙ sym (ap (m +_) (ap (_- 1) (+-sucr p n)))

-- splice respects subst on the outer vector/index.
splice-subst
  : ∀ {ℓ} {A : Type ℓ} {n n' m} (e : n ≡ n')
  → (xs : Vec A n) (i : Fin n) (ys : Vec A m)
  → splice (subst (Vec A) e xs) (subst Fin e i) ys
      ≡ subst (Vec A) (ap (λ n → m + (n - 1)) e) (splice xs i ys)
splice-subst {A = A} {m = m} e xs i ys =
  sym $ from-pathp λ t →
    splice (transport-filler (ap (Vec A) e) xs t)
           (transport-filler (ap Fin e) i t)
           ys

-- Length path for peeling splice (x ∷ xs) (fsuc i) when xs has length k + suc n.
peel-fsuc-length : ∀ m k n → m + (k + suc n) ≡ suc (m + ((k + suc n) - 1))
peel-fsuc-length m k n =
  (ap (m +_) (+-sucr k n) ∙ +-sucr m (k + n))
  ∙ (λ t → suc (sym (ap (λ l → m + (l - 1)) (+-sucr k n)) t))

-- Peel one ∷ off a splice at fsuc, when the tail length is only propositionally suc _.
--   splice (x ∷ xs) (fsuc i) ys  ≡  x ∷ splice xs i ys
splice-peel-fsuc
  : ∀ {ℓ} {A : Type ℓ} {k n m}
  → (x : A) (xs : Vec A (k + suc n)) (i : Fin (k + suc n)) (ys : Vec A m)
  → PathP (λ t → Vec A (peel-fsuc-length m k n t))
      (splice (x ∷ xs) (fsuc i) ys)
      (x ∷ splice xs i ys)
splice-peel-fsuc {A = A} {k} {n} {m} x xs i ys =
  beginᵥ[]
    splice (x ∷ xs) (fsuc i) ys
      ≡ᵥ[]⟨ (λ t → splice (x ∷ transport-filler (ap (Vec A) (+-sucr k n)) xs t)
                           (fsuc (transport-filler (ap Fin (+-sucr k n)) i t))
                           ys) ⟩
    splice (x ∷ subst (Vec A) (+-sucr k n) xs) (fsuc (subst Fin (+-sucr k n) i)) ys
      ≡ᵥ[]⟨ splice-cons-fsuc x (subst (Vec A) (+-sucr k n) xs) (subst Fin (+-sucr k n) i) ys ⟩
    x ∷ splice (subst (Vec A) (+-sucr k n) xs) (subst Fin (+-sucr k n) i) ys
      ≡ᵥ[]⟨ adjust ⟩
    x ∷ splice xs i ys ∎ᵥ
  where
    e = +-sucr k n
    e-pred = ap (λ l → m + (l - 1)) e
    suc-sym-e-pred : suc (m + (k + n)) ≡ suc (m + ((k + suc n) - 1))
    suc-sym-e-pred t = suc (sym e-pred t)

    adjust : PathP (λ t → Vec A (suc-sym-e-pred t))
      (x ∷ splice (subst (Vec A) e xs) (subst Fin e i) ys)
      (x ∷ splice xs i ys)
    adjust = to-pathp $
      subst (Vec A) suc-sym-e-pred (x ∷ splice (subst (Vec A) e xs) (subst Fin e i) ys)
        ≡⟨ subst-∷ (sym e-pred) x (splice (subst (Vec A) e xs) (subst Fin e i) ys) ⟩
      x ∷ subst (Vec A) (sym e-pred) (splice (subst (Vec A) e xs) (subst Fin e i) ys)
        ≡⟨ ap (x ∷_)
             (ap (subst (Vec A) (sym e-pred)) (splice-subst e xs i ys)
              ∙ transport⁻transport (ap (Vec A) e-pred) (splice xs i ys)) ⟩
      x ∷ splice xs i ys ∎

-- Splicing into the right summand of ++:
--   splice (ys ++ xs) (fshift m k) zs ≡ ys ++ splice xs k zs
splice-++ʳ
  : ∀ {ℓ} {A : Type ℓ} {m n p}
  → (ys : Vec A m) (xs : Vec A (suc n)) (k : Fin (suc n)) (zs : Vec A p)
  → PathP (λ t → Vec A (++ʳ-length p m n t))
      (splice (ys ++ xs) (fshift m k) zs)
      (ys ++ splice xs k zs)
splice-++ʳ {A = A} {m = zero} {n} {p} [] xs k zs =
  beginᵥ[] splice xs k zs ∎ᵥ
splice-++ʳ {A = A} {m = suc m} {n} {p} (y ∷ ys) xs k zs =
  beginᵥ[]
    splice ((y ∷ ys) ++ xs) (fshift (suc m) k) zs
      ≡ᵥ[]⟨ splice-peel-fsuc y (ys ++ xs) (fshift m k) zs ⟩
    y ∷ splice (ys ++ xs) (fshift m k) zs
      ≡ᵥ[]⟨ (λ t → y ∷ splice-++ʳ ys xs k zs t) ⟩
    y ∷ (ys ++ splice xs k zs) ∎ᵥ

lookup-shiftˡ
  : ∀ {ℓ} {A : Type ℓ} {n p}
  → (xs : Vec A (suc n)) (i k : Fin (suc n)) (i<k : i <ᶠ k) (zs : Vec A p)
  → lookup (splice xs k zs) (shift-spliceˡ {n = n} {p} {i} {k} i<k) ≡ lookup xs i
lookup-shiftˡ {n = zero} _ i k i<k _ =
  absurd (¬suc≤0 (≤-trans i<k (≤-peel (k .Fin.bounded))))
lookup-shiftˡ {n = suc n} {p} (x ∷ xs) i k i<k zs with fin-view i | fin-view k
... | _ | zero = absurd (¬suc≤0 i<k)
... | zero | suc k' =
  lookup (splice (x ∷ xs) (fsuc k') zs) (shift-spliceˡ {i = fzero} {k = fsuc k'} i<k)
    ≡⟨ lookup-pathp (splice-cons-fsuc x xs k' zs)
         (shift-spliceˡ-fzero {n} {p} k' i<k) ⟩
  lookup (x ∷ xs) fzero ∎
... | suc i' | suc k' =
  lookup (splice (x ∷ xs) (fsuc k') zs)
    (shift-spliceˡ {i = fsuc i'} {k = fsuc k'} i<k)
    ≡⟨ lookup-pathp (splice-cons-fsuc x xs k' zs)
         (shift-spliceˡ-fsuc {n} {p} {i'} {k'} i<k) ⟩
  lookup (splice xs k' zs) (shift-spliceˡ {i = i'} {k = k'} (≤-peel i<k))
    ≡⟨ lookup-shiftˡ xs i' k' (≤-peel i<k) zs ⟩
  lookup (x ∷ xs) (fsuc i') ∎

lookup-shiftʳ
  : ∀ {ℓ} {A : Type ℓ} {n m}
  → (xs : Vec A (suc n)) (i k : Fin (suc n)) (i<k : i <ᶠ k) (ys : Vec A m)
  → lookup (splice xs i ys) (shift-spliceʳ {n = n} {m} {i} {k} i<k) ≡ lookup xs k
lookup-shiftʳ {n = zero} _ i k i<k _ =
  absurd (¬suc≤0 (≤-trans i<k (≤-peel (k .Fin.bounded))))
lookup-shiftʳ {n = suc n} {m} (x ∷ xs) i k i<k ys with fin-view i | fin-view k
... | _ | zero = absurd (¬suc≤0 i<k)
... | zero | suc k' =
  lookup (ys ++ xs) (shift-spliceʳ {i = fzero} {k = fsuc k'} i<k)
    ≡⟨ ap (lookup (ys ++ xs)) (shift-spliceʳ-fzero {m = m} k' i<k) ⟩
  lookup (ys ++ xs) (fshift m k')
    ≡⟨ lookup-++ʳ ys xs k' ⟩
  lookup (x ∷ xs) (fsuc k') ∎
... | suc i' | suc k' =
  lookup (splice (x ∷ xs) (fsuc i') ys)
    (shift-spliceʳ {i = fsuc i'} {k = fsuc k'} i<k)
    ≡⟨ lookup-pathp (splice-cons-fsuc x xs i' ys)
         (shift-spliceʳ-fsuc {n} {m} {i'} {k'} i<k) ⟩
  lookup (splice xs i' ys) (shift-spliceʳ {i = i'} {k = k'} (≤-peel i<k))
    ≡⟨ lookup-shiftʳ xs i' k' (≤-peel i<k) ys ⟩
  lookup (x ∷ xs) (fsuc k') ∎

-- Double splice in either order (i before k) agrees on the flattened context.
splice-interchange
  : ∀ {ℓ} {A : Type ℓ} {n m p}
  → (xs : Vec A (suc (suc n))) (i k : Fin (suc (suc n))) (i<k : i <ᶠ k)
  → (ys : Vec A m) (zs : Vec A p)
  → PathP (λ t → Vec A (double-splice-length p m n t))
      (splice (splice xs i ys) (shift-spliceʳ {n = suc n} {m} {i} {k} i<k) zs)
      (splice (splice xs k zs) (shift-spliceˡ {n = suc n} {p} {i} {k} i<k) ys)
splice-interchange {A = A} {n} {m} {p} (x ∷ xs) i k i<k ys zs with fin-view i | fin-view k
... | _ | zero = absurd (¬suc≤0 i<k)
... | zero | suc k' =
  beginᵥ[]
    splice (ys ++ xs) (shift-spliceʳ {n = suc n} {m} {i = fzero} {k = fsuc k'} i<k) zs
      ≡ᵥ⟨ ap (λ j → splice (ys ++ xs) j zs) (shift-spliceʳ-fzero {m = m} k' i<k) ⟩
    splice (ys ++ xs) (fshift m k') zs
      ≡ᵥ[]⟨ splice-++ʳ ys xs k' zs ⟩
    ys ++ splice xs k' zs
      ≡ᵥ[]˘⟨ (λ t → splice (splice-cons-fsuc x xs k' zs t)
                            (shift-spliceˡ-fzero {n} {p} k' i<k t) ys) ⟩
    splice (splice (x ∷ xs) (fsuc k') zs)
      (shift-spliceˡ {n = suc n} {p} {i = fzero} {k = fsuc k'} i<k) ys ∎ᵥ
... | suc i' | suc k' = interchange-suc n x xs i' k' i<k ys zs
  where
    interchange-suc
      : ∀ n (x : A) (xs : Vec A (suc n)) (i' k' : Fin (suc n))
      → (i<k : fsuc i' <ᶠ fsuc k') (ys : Vec A m) (zs : Vec A p)
      → PathP (λ t → Vec A (double-splice-length p m n t))
          (splice (splice (x ∷ xs) (fsuc i') ys)
            (shift-spliceʳ {n = suc n} {m} {i = fsuc i'} {k = fsuc k'} i<k) zs)
          (splice (splice (x ∷ xs) (fsuc k') zs)
            (shift-spliceˡ {n = suc n} {p} {i = fsuc i'} {k = fsuc k'} i<k) ys)
    interchange-suc zero _ _ _ k' i<k _ _ =
      absurd (¬suc≤0 (≤-trans (≤-peel i<k) (≤-peel (k' .Fin.bounded))))
    interchange-suc (suc n) x xs i' k' i<k ys zs =
      beginᵥ[]
        splice (splice (x ∷ xs) (fsuc i') ys)
          (shift-spliceʳ {n = suc (suc n)} {m} {i = fsuc i'} {k = fsuc k'} i<k) zs
          ≡ᵥ[]⟨ (λ t → splice (splice-cons-fsuc x xs i' ys t)
                               (shift-spliceʳ-fsuc {n = suc n} {m} {i'} {k'} i<k t) zs) ⟩
        splice (x ∷ splice xs i' ys)
          (fsuc (shift-spliceʳ {n = suc n} {m} {i = i'} {k = k'} (≤-peel i<k))) zs
          ≡ᵥ[]⟨ splice-peel-fsuc {k = m} {n} {p} x
                  (splice xs i' ys)
                  (shift-spliceʳ {n = suc n} {m} {i = i'} {k = k'} (≤-peel i<k)) zs ⟩
        x ∷ splice (splice xs i' ys)
              (shift-spliceʳ {n = suc n} {m} {i = i'} {k = k'} (≤-peel i<k)) zs
          ≡ᵥ[]⟨ (λ t → x ∷ splice-interchange xs i' k' (≤-peel i<k) ys zs t) ⟩
        x ∷ splice (splice xs k' zs)
              (shift-spliceˡ {n = suc n} {p} {i = i'} {k = k'} (≤-peel i<k)) ys
          ≡ᵥ[]˘⟨ splice-peel-fsuc {k = p} {n} {m} x
                    (splice xs k' zs)
                    (shift-spliceˡ {n = suc n} {p} {i = i'} {k = k'} (≤-peel i<k)) ys ⟩
        splice (x ∷ splice xs k' zs)
          (fsuc (shift-spliceˡ {n = suc n} {p} {i = i'} {k = k'} (≤-peel i<k))) ys
          ≡ᵥ[]˘⟨ (λ t → splice (splice-cons-fsuc x xs k' zs t)
                                (shift-spliceˡ-fsuc {n = suc n} {p} {i'} {k'} i<k t) ys) ⟩
        splice (splice (x ∷ xs) (fsuc k') zs)
          (shift-spliceˡ {n = suc (suc n)} {p} {i = fsuc i'} {k = fsuc k'} i<k) ys ∎ᵥ

-- When k <ᶠ i, swap the two slots and apply splice-interchange.
splice-interchange-<
  : ∀ {ℓ} {A : Type ℓ} {n m p}
  → (xs : Vec A (suc (suc n))) (i k : Fin (suc (suc n))) (k<i : k <ᶠ i)
  → (ys : Vec A m) (zs : Vec A p)
  → PathP (λ t → Vec A (double-splice-length m p n t))
      (splice (splice xs k zs) (shift-spliceʳ {n = suc n} {p} {i = k} {k = i} k<i) ys)
      (splice (splice xs i ys) (shift-spliceˡ {n = suc n} {m} {i = k} {k = i} k<i) zs)
splice-interchange-< xs i k k<i ys zs = splice-interchange xs k i k<i zs ys
