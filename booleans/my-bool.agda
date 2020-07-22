module my-bool where -- this is just a copy of iowa bool.agda

-- recursive definition of the infinite hierarchy of Set.
open import level

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

-- 𝔹 has a type Set (type of types)
data 𝔹 : Set where
 tt : 𝔹
 ff : 𝔹

-- this is an alias for Mac users who cannot see blackboard b.
bool : Set
bool = 𝔹

-- directive for the agda compiler

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix  7 ~_
infix 6 _xor_ _nand_
infixr 6 _&&_
infixr 5 _||_
infix  4 if_then_else_   if*_then_else_
infixr 4 _imp_
infix 4 _iff_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

-- not
~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

_iff_ : 𝔹 → 𝔹 → 𝔹
tt iff tt = tt
tt iff ff = ff
ff iff tt = ff
ff iff ff = tt

-- and
_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

-- or
_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

-- { } infer type and level
-- If A := 𝔹, then ℓ is infered to level-0.
--
-- >>> :n if tt then _&&_ else _||_
-- >>> :t if tt then 𝔹 else (𝔹 → 𝔹)
-- Set (≡ Set 0)
if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then y else z = y
if ff then y else z = z

if*_then_else_ : ∀ {ℓ} {A B : Set ℓ} → (b : 𝔹) → A → B → if b then A else B
if* tt then a else b = a
if* ff then a else b = b

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor ff = tt
ff xor tt = tt
tt xor tt = ff
ff xor ff = ff

-- implication
_imp_ : 𝔹 → 𝔹 → 𝔹
tt imp b2 = b2
ff imp b2 = tt

-- also called the Sheffer stroke
_nand_ : 𝔹 → 𝔹 → 𝔹
tt nand tt = ff
tt nand ff = tt
ff nand tt = tt
ff nand ff = tt

_nor_ : 𝔹 → 𝔹 → 𝔹
x nor y = ~ (x || y)
