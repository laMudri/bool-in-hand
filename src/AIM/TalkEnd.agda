module AIM.TalkStart where

open import Algebra
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Function
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (¬_)

private
  variable
    A B X Y : Set
    P : A → Set
    x y z : A
    m n o : ℕ

infix 4 _==_

{-

Why does `Dec` look funny these days?
=====================================

James Wood  james.wood.100@strath.ac.uk
University of Strathclyde

performed alongside
Agda  github.com/agda/agda
Chalmers University of Technology

Reference: stdlib README.Decidability

This example in full:
https://personal.cis.strath.ac.uk/james.wood.100/blog/html/VecMat.html

AIM XXXII, June 2020, the Internet

-}

-- General stuff:

data Reflects (X : Set) : Bool → Set where
  ofʸ : ( x :   X) → Reflects X true
  ofⁿ : (¬x : ¬ X) → Reflects X false

record Dec (X : Set) : Set where
  constructor _because_
  field
    does : Bool
    @0 proof : Reflects X does
    -- ^ Erasure not in stdlib, but it works.
open Dec public

pattern yes x = true because ofʸ x
pattern no ¬x = false because ofⁿ ¬x

⌊_⌋ : Dec X → Bool
⌊_⌋ = does

-- Example:

_≟_ : (i j : Fin n) → Dec (i ≡ j)
zero ≟ zero = yes ≡.refl
zero ≟ suc j = no (λ ())
suc i ≟ zero = no (λ ())
does (suc i ≟ suc j) = does (i ≟ j)
proof (suc i ≟ suc j) with i ≟ j
... | no ¬x = ofⁿ (¬x ∘ suc-injective)
... | yes x = ofʸ (≡.cong suc x)

_==_ : (i j : Fin n) → Bool
i == j = ⌊ i ≟ j ⌋

==-sym : (i j : Fin n) → (i == j) ≡ (j == i)
==-sym zero    zero    = ≡.refl
==-sym zero    (suc j) = ≡.refl
==-sym (suc i) zero    = ≡.refl
==-sym (suc i) (suc j) = ==-sym i j

-- Alternative `Reflects`:

Reflects′ : (X : Set) → Bool → Set
Reflects′ X true = X
Reflects′ X false = ¬ X

record Dec′ (X : Set) : Set where
  constructor _because_
  field
    does : Bool
    proof : Reflects′ X does
open Dec′ public

pattern yes′ x = true because x
pattern no′ ¬x = false because ¬x

_≟′_ : (i j : Fin n) → Dec′ (i ≡ j)
zero ≟′ zero = yes′ ≡.refl
zero ≟′ suc j = no′ (λ ())
suc i ≟′ zero = no′ (λ ())
does (suc i ≟′ suc j) = does (i ≟′ j)
proof (suc i ≟′ suc j) with i ≟′ j  -- no `of`, but that's the only
... | false because ¬i=j = ¬i=j ∘ suc-injective  -- difference
... | true because i=j = ≡.cong suc i=j

-- Continuing with example:

module MatrixStuff (semiring : Semiring 0ℓ 0ℓ) where
  open Semiring semiring
    renaming ( Carrier to Coeff
             ; zero to annihil; zeroˡ to annihilˡ; zeroʳ to annihilʳ)
  open import Relation.Binary.Reasoning.Setoid setoid

  infixr 7 _*ₘ_
  infix 4 _≈ₘ_
  infixr -1 ∑-syntax

  Vector : ℕ → Set
  Vector n = Fin n → Coeff

  Matrix : ℕ → ℕ → Set
  Matrix m n = Fin m → Fin n → Coeff

  record _≈ₘ_ (M N : Matrix m n) : Set where
    constructor mk
    field get : ∀ i j → M i j ≈ N i j
  open _≈ₘ_ public

  -- Identity matrix
  -- ⎛1 0  ╭╮⎞
  -- ⎜0 1  ╰╯⎟
  -- ⎜╭╮  \  ⎟
  -- ⎝╰╯    1⎠
  1ₘ : Matrix n n
  1ₘ i j = if i == j then 1# else 0#

  ∑ : Vector n → Coeff
  ∑ {zero} v = 0#
  ∑ {suc n} v = v zero + ∑ (v ∘ suc)

  ∑-syntax = ∑
  syntax ∑-syntax {n} (λ j → v) = ∑ j ∈[0, n ] v

  -- Matrix multiplication
  _*ₘ_ : Matrix m n → Matrix n o → Matrix m o
  (M *ₘ N) i k = ∑ \ j → M i j * N j k

  *-distribˡ-∑ : ∀ x (v : Vector n) → x * ∑ v ≈ ∑ \ i → x * v i
  *-distribˡ-∑ {zero} x v = annihilʳ _
  *-distribˡ-∑ {suc n} x v = begin
    x * (v zero + ∑ (v ∘ suc))            ≈⟨ distribˡ _ _ _ ⟩
    x * v zero + x * ∑ (v ∘ suc)          ≈⟨ +-cong refl (*-distribˡ-∑ {n} _ _) ⟩
    x * v zero + (∑ \ i → x * v (suc i))  ∎

  test : (i j : Fin n) → Set
  test i j = Semiring.Carrier semiring

  *ₘ-identityˡ : (M : Matrix m n) → 1ₘ *ₘ M ≈ₘ M
  *ₘ-identityˡ {m = suc m} M .get zero k = begin
                                    (1ₘ *ₘ M)            zero                     k   ≡⟨⟩  -- Aut
                                    (∑ j ∈[0, suc m ] 1ₘ zero      j  * M      j  k)  ≡⟨⟩  -- oma
    1ₘ zero (zero {m}) * M zero k + (∑ j ∈[0,     m ] 1ₘ zero (suc j) * M (suc j) k)  ≡⟨⟩  -- tic
    {- work -}      1# * M zero k + (∑ j ∈[0,     m ]              0# * M (suc j) k)  ≈⟨ +-cong (*-identityˡ _) (sym (*-distribˡ-∑ {m} _ _)) ⟩
                         M zero k + 0# * (∑ j ∈[0, m ]                  M (suc j) k)  ≈⟨ +-cong refl (annihilˡ _) ⟩
                         M zero k + 0#                                                ≈⟨ +-identityʳ _ ⟩
                         M zero k                                                     ∎
  *ₘ-identityˡ {m = suc m} M .get (suc i) k = begin
                                 (1ₘ *ₘ M)            (suc i)                     k   ≡⟨⟩  -- Au
                                 (∑ j ∈[0, suc m ] 1ₘ (suc i)      j  * M      j  k)  ≡⟨⟩  -- to
    1ₘ (suc i) zero * M zero k + (∑ j ∈[0,     m ] 1ₘ (suc i) (suc j) * M (suc j) k)  ≡⟨⟩  -- ma
                 0# * M zero k + (∑ j ∈[0,     m ] 1ₘ      i       j  * M (suc j) k)  ≡⟨⟩  -- tic
    {- work -}   0# * M zero k + (1ₘ *ₘ (λ j k → M (suc j) k)) i                  k   ≈⟨ +-cong (annihilˡ _) (*ₘ-identityˡ (λ j k → M (suc j) k) .get i k) ⟩
                 0#            +                 M (suc i) k                          ≈⟨ +-identityˡ _ ⟩
                                                 M (suc i) k                          ∎
