module TalkStart where

open import Algebra
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Fin using (Fin; suc) renaming (zero to 0′)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ; suc) renaming (zero to 0′)
open import Data.Product
open import Function
open import Level using () renaming (zero to ·)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (¬_)

private
  variable
    A B X Y : Set
    P : A → Set
    x y z : A
    m n o : ℕ

infixr 6 1+_
infix 4 _==_

pattern 1+_ n = suc n

{-

A Bool in the Hand is Worth Two in the Bush
===========================================

James Wood  james.wood.100@strath.ac.uk
University of Strathclyde

performed alongside
Agda  github.com/agda/agda
Chalmers University of Technology

https://personal.cis.strath.ac.uk/james.wood.100/blog/html/VecMat.html
Agda Implementors' Meeting -- next one 1-7 April in Edinburgh!

SPLS October 2019, Glasgow

-}

-- General stuff:

-- In Haskell:
--   data Dec X = Yes X | No (Not X)
data Dec (X : Set) : Set where
  yes : ( x :   X) → Dec X
  no  : (¬x : ¬ X) → Dec X

⌊_⌋ : Dec X → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

-- Example:

_==_ : (i j : Fin n) → Bool
0′   == 0′   = true
0′   == 1+ j = false
1+ i == 0′   = false
1+ i == 1+ j = i == j

==-sym : (i j : Fin n) → (i == j) ≡ (j == i)
==-sym 0′     0′     = ≡.refl
==-sym 0′     (1+ j) = ≡.refl
==-sym (1+ i) 0′     = ≡.refl
==-sym (1+ i) (1+ j) = ==-sym i j

module MatrixStuff (semiring : Semiring · ·) where
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
  ∑ {0′} v = 0#
  ∑ {1+ n} v = v 0′ + ∑ (v ∘ 1+_)

  ∑-syntax = ∑
  syntax ∑-syntax {n} (λ j → v) = ∑ j ∈[0, n ] v

  -- Matrix multiplication
  _*ₘ_ : Matrix m n → Matrix n o → Matrix m o
  (M *ₘ N) i k = ∑ \ j → M i j * N j k

  *-distribˡ-∑ : ∀ x (v : Vector n) → x * ∑ v ≈ ∑ \ i → x * v i
  *-distribˡ-∑ {0′} x v = annihilʳ _
  *-distribˡ-∑ {1+ n} x v = begin
    x * (v 0′ + ∑ (v ∘ 1+_))           ≈⟨ distribˡ _ _ _ ⟩
    x * v 0′ + x * ∑ (v ∘ 1+_)         ≈⟨ +-cong refl (*-distribˡ-∑ {n} _ _) ⟩
    x * v 0′ + (∑ \ i → x * v (1+ i))  ∎

  *ₘ-identityˡ : (M : Matrix m n) → 1ₘ *ₘ M ≈ₘ M
  *ₘ-identityˡ {m = 1+ m} M .get 0′ k = begin
                              (1ₘ *ₘ M)           0′                   k   ≡⟨⟩  -- Aut
                              (∑ j ∈[0, 1+ m ] 1ₘ 0′     j  * M     j  k)  ≡⟨⟩  -- oma
    1ₘ 0′ (0′ {m}) * M 0′ k + (∑ j ∈[0,    m ] 1ₘ 0′ (1+ j) * M (1+ j) k)  ≡⟨⟩  -- tic
  {- work -}    1# * M 0′ k + (∑ j ∈[0,     m ]          0# * M (1+ j) k)  ≈⟨ +-cong (*-identityˡ _) (sym (*-distribˡ-∑ {m} _ _)) ⟩
                     M 0′ k + 0# * (∑ j ∈[0, m ]              M (1+ j) k)  ≈⟨ +-cong refl (annihilˡ _) ⟩
                     M 0′ k + 0#                                           ≈⟨ +-identityʳ _ ⟩
                     M 0′ k                                                ∎
  *ₘ-identityˡ {m = 1+ m} M .get (1+ i) k = begin
                            (1ₘ *ₘ M)           (1+ i)                   k   ≡⟨⟩  -- Au
                            (∑ j ∈[0, 1+ m ] 1ₘ (1+ i)     j  * M     j  k)  ≡⟨⟩  -- to
    1ₘ (1+ i) 0′ * M 0′ k + (∑ j ∈[0,    m ] 1ₘ (1+ i) (1+ j) * M (1+ j) k)  ≡⟨⟩  -- ma
              0# * M 0′ k + (∑ j ∈[0,    m ] 1ₘ     i      j  * M (1+ j) k)  ≡⟨⟩  -- tic
  {- work -}  0# * M 0′ k + (1ₘ *ₘ (λ j k → M (1+ j) k)) i               k   ≈⟨ +-cong (annihilˡ _) (*ₘ-identityˡ (λ j k → M (1+ j) k) .get i k) ⟩
              0#          +                 M (1+ i) k                       ≈⟨ +-identityˡ _ ⟩
                                            M (1+ i) k                       ∎
