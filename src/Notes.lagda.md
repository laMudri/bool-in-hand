```agda
module Notes where

  open import Relation.Nullary using (¬_)
```

# Notes

The transformation applied to `Dec`:

```agda
  module Dec-Before where

    data Dec {x} (X : Set x) : Set x where
      yes :  (x :   X) → Dec X
      no  : (¬x : ¬ X) → Dec X

  module Dec-After where

    data DecDatum : Set where
      yes-datum : DecDatum
      no-datum  : DecDatum

    data DecIndexed {x} (X : Set x) : DecDatum → Set x where
      yes-indexed : (x  :   X) → DecIndexed X yes-datum
      no-indexed  : (¬x : ¬ X) → DecIndexed X no-datum

    record Dec {x} (X : Set x) : Set x where
      constructor mkDec
      field
        datum : DecDatum
        proof : DecIndexed X datum

    pattern yes x = mkDec yes-datum (yes-indexed x)
    pattern no ¬x = mkDec  no-datum (no-indexed ¬x)
```

To `List`:
```agda
  module List-Before where

    infixr 5 _∷_

    data List {x} (X : Set x) : Set x where
      [] : List X
      _∷_ : (x : X) (xs : List X) → List X

  module List-After where

    infixr 5 _∷_ _∷-indexed_

    data ListDatum : Set where
      []-datum : ListDatum
      ∷-datum : ListDatum → ListDatum

    data ListIndexed {x} (X : Set x) : ListDatum → Set x where
      []-indexed : ListIndexed X []-datum
      _∷-indexed_ : ∀ {n} (x : X) (xs : ListIndexed X n) →
                    ListIndexed X (∷-datum n)

    record List {x} (X : Set x) : Set x where
      constructor mkList
      field
        {datum} : ListDatum
        proof : ListIndexed X datum
    open List public

    pattern [] = mkList []-datum []-indexed
    pattern _∷_ x xs = mkList (∷-datum _) (x ∷-indexed xs)

    map-indexed : ∀ {x y} {X : Set x} {Y : Set y} (f : X → Y) →
                  ∀ {n} → (ListIndexed X n → ListIndexed Y n)
    map-indexed f []-indexed = []-indexed
    map-indexed f (x ∷-indexed xs) = f x ∷-indexed map-indexed f xs

    map : ∀ {x y} {X : Set x} {Y : Set y} (f : X → Y) → (List X → List Y)
    map f (mkList xs) = mkList (map-indexed f xs)
```

Bob's example: lists with a preserved sum
```agda
  module List-Sum where

    open import Data.Nat.Base

    open List-Before

    infixr 5 _∷_ _#∷_

    sum : List ℕ → ℕ
    sum [] = 0
    sum (n ∷ ns) = n + sum ns

    data ListWithSum : ℕ → Set where
      [] : ListWithSum 0
      _∷_ : ∀ {∑ns} (n : ℕ) (ns : ListWithSum ∑ns) → ListWithSum (n + ∑ns)

    record List# : Set where
      constructor mkList#
      field
        {datum} : ℕ
        proof : ListWithSum datum

    pattern #[] = mkList# []
    pattern _#∷_ n ns = mkList# (n ∷ ns)

    -- map : List# → List#
```

A more constructively useful version of `Dec`:
```agda
  module ConstructiveDec where

    open import Data.Empty
    open import Function using (id)
    open import Level using (_⊔_)

    infixr 1 _⊎_
    infix 4 _≈_ _≉_

    data Dir : Set where
      left right : Dir

    data SumI {a b} (A : Set a) (B : Set b) : Dir → Set (a ⊔ b) where
      inl : A → SumI A B left
      inr : B → SumI A B right

    record _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
      constructor mk⊎
      field
        {dir} : Dir
        cont : SumI A B dir
    open _⊎_ public

    record Mutex {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
      constructor mkMutex
      field
        contradiction : A → B → ⊥

    record CDec {a b} {A : Set a} {B : Set b} (c : A → B → ⊥)
                : Set (a ⊔ b) where
      constructor mkCDec
      field
        {dir} : Dir
        proof : SumI A B dir

    map⊎ : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} →
           (A → A′) → (B → B′) → A ⊎ B → A′ ⊎ B′
    dir (map⊎ f g ab) = dir ab
    cont (map⊎ f g (mk⊎ (inl a))) = inl (f a)
    cont (map⊎ f g (mk⊎ (inr b))) = inr (g b)

    Dec : ∀ {a} (A : Set a) → Set a
    Dec A = CDec {B = A} id

    open import Data.Nat.Base

    data _≈_ : (m n : ℕ) → Set where
      zero : zero ≈ zero
      suc : ∀ {m n} → m ≈ n → suc m ≈ suc n

    data _≉_ : (m n : ℕ) → Set where
      z≉s : ∀ {n} → zero ≉ suc n
      s≉z : ∀ {m} → suc m ≉ zero
      s≉s : ∀ {m n} → m ≉ n → suc m ≉ suc n

    ≉-≈ : ∀ {m n} → m ≉ n → m ≈ n → ⊥
    ≉-≈ (s≉s neq) (suc eq) = ≉-≈ neq eq

    _≈?_ : ∀ m n → m ≉ n ⊎ m ≈ n
    zero ≈? zero = mk⊎ (inr zero)
    zero ≈? suc n = mk⊎ (inl z≉s)
    suc m ≈? zero = mk⊎ (inl s≉z)
    suc m ≈? suc n = map⊎ s≉s suc (m ≈? n)

    test : (m n : ℕ) → Set
    test m n = {!dir (suc (suc m) ≈? suc (suc (suc n)))!}
```
