open import 1Lab.Prelude hiding (map)
open import Data.Nat
open import Data.Fin.Base
open import Data.Fin.Extra
open import Data.Vec.Base as Vec hiding (_++_)
open import Data.Vec.Properties

module Data.Vec.Extra where

-- 1lab's Data.Vec.Base leaves _++_ without a fixity. Agda forbids fixity
-- decls on imported names, so re-export a local synonym instead.
infixr 8 _++_
_++_ : ∀ {ℓ} {A : Type ℓ} {n k} → Vec A n → Vec A k → Vec A (n + k)
_++_ = Vec._++_

-- PathP analogue of Vec-path from Data.Vec.Properties.
Vec-pathp
  : ∀ {ℓ} {A : Type ℓ} {n : I → Nat} {v : Vec A (suc (n i0))} {w : Vec A (suc (n i1))}
  → PathP (λ i → A) (head v) (head w)
  → PathP (λ i → Vec A (n i)) (tail v) (tail w)
  → PathP (λ i → Vec A (suc (n i))) v w
Vec-pathp {v = x ∷ xs} {w = y ∷ ys} h t i = h i ∷ t i

-- Compose PathPs of vectors along concatenated length paths.
vec∙P
  : ∀ {ℓ} {A : Type ℓ} {n₀ n₁ n₂}
  → {p : n₀ ≡ n₁} {q : n₁ ≡ n₂}
  → {xs : Vec A n₀} {ys : Vec A n₁} {zs : Vec A n₂}
  → PathP (λ t → Vec A (p t)) xs ys
  → PathP (λ t → Vec A (q t)) ys zs
  → PathP (λ t → Vec A ((p ∙ q) t)) xs zs
vec∙P {p = p} {q} = _∙P_ {A = Nat} {B = Vec _} {p = p} {q = q}

-- Equational-reasoning sugar for vec∙P, in the style of displayed
-- categories' _∫≡_ / ≡[ p ]⟨ ⟩ / ∎[] (Cat.Displayed.Base).
--
-- A chain builds a path in the total space Σ Nat (Vec A); beginᵥ[]_
-- projects to a PathP over a chosen length path via Nat-is-set.
module _ {ℓ} {A : Type ℓ} where
  _∫≡ᵥ_ : ∀ {n m} → Vec A n → Vec A m → Type ℓ
  _∫≡ᵥ_ {n} {m} xs ys = Path (Σ Nat (Vec A)) (n , xs) (m , ys)

  beginᵥ_
    : ∀ {n m} {xs : Vec A n} {ys : Vec A m}
    → (p : xs ∫≡ᵥ ys)
    → PathP (λ i → Vec A (ap fst p i)) xs ys
  beginᵥ_ p i = p i .snd

  beginᵥ[]_
    : ∀ {n m} {xs : Vec A n} {ys : Vec A m} {q : n ≡ m}
    → xs ∫≡ᵥ ys
    → PathP (λ i → Vec A (q i)) xs ys
  beginᵥ[]_ {q = q} p =
    is-set→cast-pathp (Vec A) Nat-is-set (beginᵥ p)

  ≡ᵥ[-]⟨⟩-syntax
    : ∀ {n₀ n₁ n₂} (xs : Vec A n₀) (p : n₀ ≡ n₁)
    → {ys : Vec A n₁} {zs : Vec A n₂}
    → ys ∫≡ᵥ zs
    → PathP (λ i → Vec A (p i)) xs ys
    → xs ∫≡ᵥ zs
  ≡ᵥ[-]⟨⟩-syntax _ p rest step =
    Σ-pathp (p ∙ ap fst rest)
      (vec∙P {p = p} {q = ap fst rest} step (beginᵥ rest))

  ≡ᵥ[]⟨⟩-syntax
    : ∀ {n₀ n₁ n₂} (xs : Vec A n₀)
    → {p : n₀ ≡ n₁} {ys : Vec A n₁} {zs : Vec A n₂}
    → ys ∫≡ᵥ zs
    → PathP (λ i → Vec A (p i)) xs ys
    → xs ∫≡ᵥ zs
  ≡ᵥ[]⟨⟩-syntax xs {p = p} rest step = ≡ᵥ[-]⟨⟩-syntax xs p rest step

  ≡ᵥ[]˘⟨⟩-syntax
    : ∀ {n₀ n₁ n₂} (xs : Vec A n₀)
    → {p : n₁ ≡ n₀} {ys : Vec A n₁} {zs : Vec A n₂}
    → ys ∫≡ᵥ zs
    → PathP (λ i → Vec A (p i)) ys xs
    → xs ∫≡ᵥ zs
  ≡ᵥ[]˘⟨⟩-syntax xs rest step = ≡ᵥ[]⟨⟩-syntax xs rest (symP step)

  -- Homogeneous step (length path = refl), like ordinary ≡⟨ ⟩.
  ≡ᵥ⟨⟩-syntax
    : ∀ {n m} (xs : Vec A n) {ys : Vec A n} {zs : Vec A m}
    → ys ∫≡ᵥ zs
    → xs ≡ ys
    → xs ∫≡ᵥ zs
  ≡ᵥ⟨⟩-syntax xs rest step = ≡ᵥ[-]⟨⟩-syntax xs refl rest (λ i → step i)

  _∎ᵥ : ∀ {n} (xs : Vec A n) → xs ∫≡ᵥ xs
  _∎ᵥ _ = refl

  infix 1 beginᵥ_ beginᵥ[]_
  infixr 2 ≡ᵥ[-]⟨⟩-syntax ≡ᵥ[]⟨⟩-syntax ≡ᵥ[]˘⟨⟩-syntax ≡ᵥ⟨⟩-syntax
  infix 3 _∎ᵥ

  syntax ≡ᵥ[-]⟨⟩-syntax xs p rest step = xs ≡ᵥ[ p ]⟨ step ⟩ rest
  syntax ≡ᵥ[]⟨⟩-syntax xs rest step = xs ≡ᵥ[]⟨ step ⟩ rest
  syntax ≡ᵥ[]˘⟨⟩-syntax xs rest step = xs ≡ᵥ[]˘⟨ step ⟩ rest
  syntax ≡ᵥ⟨⟩-syntax xs rest step = xs ≡ᵥ⟨ step ⟩ rest

-- subst along ap suc commutes with ∷
subst-∷
  : ∀ {ℓ} {A : Type ℓ} {n m} (q : n ≡ m) (x : A) (xs : Vec A n)
  → subst (Vec A) (ap suc q) (x ∷ xs) ≡ x ∷ subst (Vec A) q xs
subst-∷ {A = A} q x xs =
  from-pathp λ t → x ∷ transport-filler (ap (Vec A) q) xs t

++-zeror : ∀ {ℓ} {A : Type ℓ} {n : Nat} {Γ : Vec A n} → PathP (λ i → Vec A (+-zeror n i)) (Γ ++ []) Γ
++-zeror {Γ = []} = refl
++-zeror {Γ = x ∷ []} = refl
++-zeror {A = A} {Γ = x ∷ y ∷ Γ} =
  beginᵥ[]
    x ∷ ((y ∷ Γ) ++ []) ≡ᵥ[]⟨ Vec-pathp refl (++-zeror {Γ = y ∷ Γ}) ⟩
    x ∷ (y ∷ Γ) ∎ᵥ

++-associative
  : ∀ {ℓ} {A : Type ℓ} {p m n}
  → (xs : Vec A p) (ys : Vec A m) (zs : Vec A n)
  → PathP (λ t → Vec A (+-associative p m n t))
      (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
++-associative [] ys zs = refl
++-associative {A = A} (x ∷ xs) ys zs =
  beginᵥ[]
    x ∷ (xs ++ (ys ++ zs)) ≡ᵥ[]⟨ Vec-pathp refl (++-associative xs ys zs) ⟩
    x ∷ ((xs ++ ys) ++ zs) ∎ᵥ

-- Congruence of _++_ in the left argument along a length path
++-congˡ
  : ∀ {ℓ} {A : Type ℓ} {m₀ m₁ n} {q : m₀ ≡ m₁}
  → {xs : Vec A m₀} {ys : Vec A m₁}
  → PathP (λ t → Vec A (q t)) xs ys
  → (zs : Vec A n)
  → PathP (λ t → Vec A (ap (_+ n) q t)) (xs ++ zs) (ys ++ zs)
++-congˡ p zs t = p t ++ zs

-- lookup into the left summand of ++
lookup-++ˡ
  : ∀ {ℓ} {A : Type ℓ} {m n}
  → (xs : Vec A (suc m)) (ys : Vec A n) (i : Fin (suc m))
  → lookup (xs ++ ys) (inject (s≤s (+-≤l m n)) i) ≡ lookup xs i
lookup-++ˡ (x ∷ xs) ys i with fin-view i
... | zero = refl
lookup-++ˡ {m = suc m} (x ∷ xs) ys i | suc j =
  lookup ((x ∷ xs) ++ ys) (inject (s≤s (+-≤l (suc m) _)) (fsuc j))
    ≡⟨ ap (lookup ((x ∷ xs) ++ ys)) (inject-fsuc j) ⟩
  lookup (xs ++ ys) (inject (s≤s (+-≤l m _)) j)
    ≡⟨ lookup-++ˡ xs ys j ⟩
  lookup xs j ∎

-- lookup into the right summand of ++
lookup-++ʳ
  : ∀ {ℓ} {A : Type ℓ} {m n}
  → (xs : Vec A m) (ys : Vec A n) (j : Fin n)
  → lookup (xs ++ ys) (fshift m j) ≡ lookup ys j
lookup-++ʳ [] ys j = refl
lookup-++ʳ (x ∷ xs) ys j = lookup-++ʳ xs ys j
