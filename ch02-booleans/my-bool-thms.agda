module my-bool-thms where

open import bool
open import eq
open import sum


-- ~ ~ tt ≡ tt
-- >>> ,t
-- Set
~~tt : ~ ~ tt ≡ tt
~~tt = refl -- reflexivity

-- refl uses an implicit argument
-- this is why ~~tt is not equal to ~~ff

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl -- ~~tt is also valid
~~-elim ff = refl

-- Agda infers the type for b.
&&-idem : ∀ {b} → b && b ≡ b
&&-idem{tt} = refl -- pattern-matching on implicit arguments.
&&-idem{ff} = refl

test-&&-idem : tt && tt ≡ tt
test-&&-idem = &&-idem -- &&-idem{tt} in case it could not be infered.

-- To instantitate A to 𝔹, without explicitly instantiating ℓ, we can write
--
-- // if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
-- if_then_else{A = 𝔹}
--
-- Then we will se the type 𝔹 → 𝔹 → 𝔹 → 𝔹

||-idem : ∀{b} → b || b ≡ b
||-idem{tt} = refl
||-idem{ff} = refl

-- Under the Curry-Howard isomorphism, to express an assumption, we write a function that takes in a proof of that assumption, and then produces the proof of the desired result.
--
-- Assumption = b1 || b2 ≡ ff
-- Desired result = b1 ≡ ff
--
-- absurd pattern ()
--
--    We can use it because the assumption is impossible :: tt || b2 ≡ ff  definitionally equal to tt ≡ ff
--    "quit early" when we have an abviously impossible assumption.
--    No need to proof this case.
--
||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → ff ≡ b1
||≡ff₁ {ff} p = refl -- p : proof for assumption
                     -- refl because if b1 ≡ ff then the result is b1 itself.
                     -- refl to proof the trivial equation ff ≡ ff
||≡ff₁ {tt} p = sym p -- ||≡ff₁ {tt} ()
                      -- ||≡ff₁ {tt} p = p -- You need to change ff ≡ b1 to b1 ≡ ff
                      --                   -- this is why we used sym p (sym means symmetry)
                      --                   -- sym takes x ≡ y and returns y ≡ x
-- ^^^ ∀ {b2} → tt || b2 ≡ ff → tt ≡ ff

-- ||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → ff ≡ b1
-- ||≡ff₁ refl = refl
-- Type refinements doesn't work on non-variable types.
-- Agda can't conclude that b1 || b2 is definitionally equal to ff.


||≡ff₂ : ∀ {b1 b2} → b1 || b2 ≡ ff → b2 ≡ ff
||≡ff₂ {tt} ()
||≡ff₂ {ff}{tt} ()
||≡ff₂ {ff}{ff} p = refl

||-tt : ∀ (b : 𝔹) → b || tt ≡ tt
||-tt tt = refl
||-tt ff = refl

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
||-cong₁ refl = refl -- After assumption, (b1 || b2) ≡ (b1 || b2) is trivial

-- ||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
-- ||-cong₁ {b1}{b1'}{b2} refl = refl -- ko
-- ||-cong₁ {b1}{.b1}{b2} refl = refl -- ok (the term is not a subpattern to match).

-- goal: formula whih we have to prove on the rhs.

-- another approach: rewrite
||-cong₂ : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
||-cong₂ p rewrite p = refl
-- rewrite: replace every occurence of the rewrite p of the lhs with the rhs.
--          In this example: b2 by b2' so the goal becomes b1 || b2' ≡ b1 || b2' which is trivial.

-- The rewrite p instructs the Agda type checker to look in the goal for any occurences of X, and transform those into Y.
--
-- X and Y could be complex expressions; they do not have to be just variables.

ite-same : ∀{ℓ}{A : Set ℓ} →
           ∀(b : 𝔹) (x : A) →
           (if b then x else x) ≡ x
ite-same tt x = refl -- ∀ (x : A) → x ≡ x
ite-same ff x = refl -- ∀ (x : A) → x ≡ x

ite-arg : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (f : A → B)(b : 𝔹)(x y : A) → (f (if b then x else y)) ≡ (if b then f x else f y)
ite-arg f tt x y = refl
ite-arg f ff x y = refl

-- absurd assumption, absurd pattern.
--
-- If ff ≡ tt, then the universal formula is true (but we know this is false, otherwise all formulas are true)
𝔹-contra : ff ≡ tt → ∀{ℓ} {P : Set ℓ} → P
𝔹-contra ()

||-split : ∀ {b b' : 𝔹} → b || b' ≡ tt → b ≡ tt ⊎ b' ≡ tt
||-split{tt}{tt} p = inj₁ refl
||-split{tt}{ff} p = inj₁ refl
||-split{ff}{tt} p = inj₂ refl
||-split{ff}{ff} ()

𝔹-dec : ∀ (b : 𝔹) → b ≡ tt ⊎ b ≡ ff
𝔹-dec tt = inj₁ refl
𝔹-dec ff = inj₂ refl

&&-snd : {p1 p2 : 𝔹} → p1 && p2 ≡ tt → p2 ≡ tt
&&-snd{tt} p = p
&&-snd{ff} ()

&&-fst : {p1 p2 : 𝔹} → p1 && p2 ≡ tt → p1 ≡ tt
&&-fst{tt} p = refl
&&-fst{ff} ()

&&-combo : {p1 p2 : 𝔹} → p1 ≡ tt → p2 ≡ tt → p1 && p2 ≡ tt
&&-combo{tt} pr1 pr2 = pr2
&&-combo{ff} pr1 pr2 = 𝔹-contra pr1

&&-ff : ∀(b : 𝔹) → b && ff ≡ ff
&&-ff tt = refl
&&-ff ff = refl

-------------------------------------------------------
-------------------------------------------------------

-- Exercises

-- 1
||-combo : {p1 p2 : 𝔹} → p1 ≡ ff → p2 ≡ ff → p1 || p2 ≡ ff
||-combo{ff} pr1 pr2 = pr2
||-combo{tt} () -- ||-combo{tt} pr1 pr2 = 𝔹-contra (sym pr1)

-- 2
deMorgan : ∀ {b₁ b₂} → ~ (b₁ || b₂) ≡ ~ b₁ && ~ b₂
deMorgan{tt} = refl
deMorgan{ff} = refl
