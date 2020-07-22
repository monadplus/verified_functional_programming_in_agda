module demo1A where

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
-- ,c  case analysis
if true then t else e = t -- ,g give
if false then t else e = e -- ,a auto

data ℕ : Set where
  Zero : ℕ
  Suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
Zero + y = y
Suc x + y = Suc (x + y)

data Vec (A : Set) : ℕ → Set where
  Empty : Vec A Zero
  Cons : {n : ℕ} → A → Vec A n → Vec A (Suc n)

-- ,e environment   (try it on the first case by deleting the body)
vConcat : {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
vConcat {A} {Zero} v1 v2 = v2
vConcat {A} {Suc x} (Cons x₁ x₂) v2 = Cons x₁ (vConcat x₂ v2)

low = Suc Zero

-- ,n   normalize expression
high = low + low

-- ,t  type of an expression

-- :make to compile
