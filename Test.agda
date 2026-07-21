{-# OPTIONS --cubical #-}

module Test where

open import 1Lab.Prelude

module _ {A : Type} (f : {a : A} → A) (x y : A) (p : x ≡ y) where
  g : f {x} ≡ f {y}
  g i = {! !}


data Vec (A : Type) : Nat → Type where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

mapVec : {A B : Type} {n : Nat} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

append : {A : Type} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

example : Vec Nat 3
example =
  let xs : Vec Nat 2
      xs = 1 ∷ (2 ∷ [])

      ys : Vec Nat 1
      ys = 3 ∷ []

      zs = append xs ys
  in {! zs !}
