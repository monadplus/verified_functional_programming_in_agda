module my-list-thms where

-- see list-thms2 for more

open import bool
open import bool-thms
open import functions
open import list
open import nat
open import nat-thms
open import product-thms
open import logic

++[] : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → l ++ [] ≡ l
++[] [] = refl
++[] (x :: xs) rewrite ++[] xs = refl

++-assoc : ∀ {ℓ}{A : Set ℓ} (l1 l2 l3 : 𝕃 A) →
           (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: xs) l2 l3 rewrite ++-assoc xs l2 l3 = refl
-- (x :: (xs ++ l2) ++ l3 ≡ x :: xs ++ l2 ++ l3

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) →
            length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (h :: t) l2 rewrite length-++ t l2 = refl
--suc (length (t ++ l2)) ≡ suc (length t + length l2)

map-append : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
             (f : A → B) (l1 l2 : 𝕃 A) →
             map f (l1 ++ l2) ≡ (map f l1) ++ (map f l2)
map-append f [] l2 = refl
map-append f (x :: xs) l2 rewrite map-append f xs l2 = refl

map-compose : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''} →
             (f : B → C) (g : A → B) (l : 𝕃 A) →
             map f (map g l) ≡ map (f ∘ g) l
map-compose f g [] = refl
map-compose f g (x :: xs) rewrite map-compose f g xs = refl

foldr-append : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}{l₁ l₂ : 𝕃 (A → 𝕃 B)}{a : A}
  → (foldr (λ f → _++_ (f a)) [] l₁) ++ (foldr (λ f → _++_ (f a)) [] l₂) ≡ foldr (λ f → _++_ (f a)) [] (l₁ ++ l₂)
foldr-append {l₁ = []}{_}{a} = refl
foldr-append {l₁ = x :: l₁}{l₂}{a}
 rewrite
    ++-assoc (x a) (foldr (λ f → _++_ (f a)) [] l₁) (foldr (λ f → _++_ (f a)) [] l₂)
  | foldr-append {l₁ = l₁}{l₂}{a}
 = refl

invert𝕃 : ∀{ℓ}{A : Set ℓ}{t : A}{ts : 𝕃 A} → t :: ts ≢ []
invert𝕃 ()

length-repeat : ∀{ℓ}{A : Set ℓ} (n : ℕ) (a : A) → length (repeat n a) ≡ n
length-repeat 0 a = refl
length-repeat (suc n) a rewrite length-repeat n a = refl

map-repeat : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(n : ℕ)(a : A)(f : A → B) → map f (repeat n a) ≡ repeat n (f a)
map-repeat 0 a f = refl
map-repeat (suc x) a f rewrite map-repeat x a f = refl

length-map : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)(l : 𝕃 A) → length (map f l) ≡ length l
length-map f [] = refl
length-map f (head :: tail) rewrite length-map f tail = refl








-- We need this lemma to prove length-reverse
length-reverse-helper : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) →
                      length (reverse-helper h l) ≡ length h + length l
length-reverse-helper h [] rewrite +0 (length h) = refl
-- length h ≡ length h + 0
length-reverse-helper h (x :: xs) rewrite length-reverse-helper (x :: h) xs = ?
  -- sym (+suc (length h) (length xs))
-- length (reverse-helper (x :: h) xs) ≡ length h + suc (length xs)
-- suc (length g + length xs) ≡ length h + suc (length xs)              (induction)
-- length g + suc (length xs) ≡ length h + suc (length xs)              (+suc)

length-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
length-reverse l = length-reverse-helper [] l
-- length (reverse-helper [] l) ≡ length l
-- length [] + length l ≡ length l            (length-reverse-helper)
-- 0 + length l ≡ length l
-- length l ≡ length l













reverse-++h : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse-helper l1 l2 ≡ reverse-helper [] l2 ++ l1
reverse-++h l1 [] = refl
reverse-++h l1 (x :: xs) rewrite reverse-++h (x :: l1) xs | reverse-++h (x :: []) xs | ++-assoc (reverse xs) (x :: []) l1 = refl

reverse-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse(l1 ++ l2) ≡ reverse(l2) ++ reverse(l1)
reverse-++ [] l2 rewrite ++[] (reverse l2) = refl
reverse-++ (x :: xs) l2 rewrite reverse-++h (x :: []) (xs ++ l2) | reverse-++ xs l2 | ++-assoc (reverse l2) (reverse xs) (x :: []) | sym (reverse-++h (x :: []) xs) = refl

=𝕃-refl : ∀{ℓ}{A : Set ℓ}{l1 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → x ≡ y → eq x y ≡ tt) → =𝕃 eq l1 l1 ≡ tt
=𝕃-refl{l1 = []} eq rise = refl
=𝕃-refl{l1 = x :: xs} eq rise = &&-combo (rise x x refl) (=𝕃-refl{l1 = xs} eq rise)

≡𝕃-from-= : ∀{ℓ}{A : Set ℓ}{l1 l2 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → eq x y ≡ tt → x ≡ y) → =𝕃 eq l1 l2 ≡ tt → l1 ≡ l2
≡𝕃-from-={l1 = []}{[]} eq drop p = refl
≡𝕃-from-={l1 = x :: xs}{[]} eq drop ()
≡𝕃-from-={l1 = []}{y :: ys} eq drop ()
≡𝕃-from-={l1 = x :: xs}{y :: ys} eq drop p rewrite ≡𝕃-from-={l1 = xs} eq drop (&&-snd{eq x y}{=𝕃 eq xs ys} p) |  drop x y (&&-fst p) = refl

=𝕃-from-≡ : ∀{ℓ}{A : Set ℓ}{l1 l2 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → x ≡ y → eq x y ≡ tt) → l1 ≡ l2  → =𝕃 eq l1 l2 ≡ tt
=𝕃-from-≡{l2 = l2} eq rise p rewrite p  = =𝕃-refl{l1 = l2} eq rise

multi++-assoc : ∀{ℓ}{A : Set ℓ} → (Ls : 𝕃 (𝕃 A)) → (l0 : 𝕃 A) → (foldr _++_ [] Ls) ++ l0 ≡ (foldr _++_ [] (Ls ++ [ l0 ]))
multi++-assoc [] l' rewrite ++[] l' = refl
multi++-assoc (l :: ls) l' rewrite ++-assoc l (foldr _++_ [] ls) l' | multi++-assoc ls l' = refl

concat-foldr : ∀{ℓ}{A : Set ℓ} → (ls : 𝕃 (𝕃 A)) → (l : 𝕃 A) → concat ls ++ l ≡ foldr _++_ l ls
concat-foldr [] l = refl
concat-foldr (l' :: ls) l rewrite ++-assoc l' (concat ls) l | concat-foldr ls l = refl

--concat-foldr (l' :: (l'' :: ls)) l rewrite ++-assoc l' (concat (l'' :: ls)) l | concat-foldr (l'' :: ls) l = refl

longer-trans : ∀{ℓ}{A : Set ℓ}(l1 l2 l3 : 𝕃 A) →
                l1 longer l2 ≡ tt →
                l2 longer l3 ≡ tt →
                l1 longer l3 ≡ tt
longer-trans [] l2 l3 () q
longer-trans (x :: l1) [] l3 p ()
longer-trans (x :: l1) (x₁ :: l2) [] p q = refl
longer-trans (x :: l1) (x₁ :: l2) (x₂ :: l3) p q = longer-trans l1 l2 l3 p q





-- keep (iowa std)/inspect (Agda std)
filter-idem : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
              (filter p (filter p l)) ≡ (filter p l)
filter-idem p [] = refl
filter-idem p (x :: l) with keep (p x)
-- filter p (if px then x :: filter p l else filter p l) ≡ if p x then x :: filter p l else filter p l
filter-idem p (x :: l) | tt , p' rewrite p' | p' | filter-idem p l = refl
-- Agda simplified this way:
--   filter p (x :: filter p l) ≡ x :: filter p l
-- Which can be further normalized applying the filter definition:
--   if p x then x :: filter p (filter p l) else filter p (filter p l) ≡ x :: filter p l
-- If subsequent normalization steps (using definitional equality) produce that expression again,
--  Agda will not instantiate it again.
-- The keep/inspect idiom is a cute way around this.
-- Now p' : p x ≡ tt
-- Agda will not actually instantitate p x in the goal when we do a keep.
-- We have to apply an explicit rewrite p'
-- Now the goal is:
--   if p x then x :: filter p (filter p l) else filter p (filter p l) ≡ x :: filter p l
-- Another rewrite p':
--   x :: filter p (filter p l) ≡ x :: filter p l
filter-idem p (x :: l) | ff , p' rewrite p' = filter-idem p l





length-filter : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
                length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x :: l) with p x
-- Goal:
--   length (if px then x :: filter p l else filter p l) < suc (length l ....
--   ^^^ This is the normalized version of ≤
-- So we can undo the process:
--  length (if px then x :: filter p l else filter p l) ≤ suc (length l)
length-filter p (x :: l) | tt rewrite length-filter p l = refl
length-filter p (x :: l) | ff = ≤-trans{length (filter p l)} (length-filter p l) (≤-suc (length l))
-- Goal: length (filter p l) ≤ suc (length l) ≡ tt
--
-- We have the theorems:
--     - induction hypothesis: length (filter p l) ≤ length l ≡ tt
--     - ≤-suc: n ≤ suc n ≡ tt (length l ≤ suc (length l) ≡ tt)
--
-- The facts look like these x ≤ y and y ≤ z, where
--  - x is length (filter p l)
--  - y is length l
--  - z is suc (length l)
--
-- We need to apply ≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y ≤ z ≡ tt → x ≤ z ≡ tt
--   with our theorems to get the goal.
--
-- (!) You need to specify the implicit argument because Agda can infer the value for x.




filter-++ : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l1 l2 : 𝕃 A) → filter p (l1 ++ l2) ≡ filter p l1 ++ filter p l2
filter-++ p [] l2 = refl
filter-++ p (x :: l1) l2 with p x
filter-++ p (x :: l1) l2 | tt rewrite (filter-++ p l1 l2) = refl
filter-++ p (x :: l1) l2 | ff rewrite (filter-++ p l1 l2) = refl

remove-++ : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) →
            remove eq a (l1 ++ l2) ≡ remove eq a l1 ++ remove eq a l2
remove-++ eq a l1 l2 = filter-++ (λ x → ~ (eq a x)) l1 l2

::-injective : ∀{ℓ}{A : Set ℓ}{x y : A}{xs ys : 𝕃 A} →
               x :: xs ≡ y :: ys → x ≡ y ∧ xs ≡ ys
::-injective refl = refl , refl

concat-++ : ∀{ℓ}{A : Set ℓ}(ls1 ls2 : 𝕃 (𝕃 A)) → concat (ls1 ++ ls2) ≡ (concat ls1) ++ (concat ls2)
concat-++ [] ls2 = refl
concat-++ (l :: ls) ls2 rewrite concat-++ ls ls2 = sym (++-assoc l (concat ls) (concat ls2))

-- This holds as long as we have the equations p₁ and p₂.  We know
-- that these equations are consistant to adopt, because they are
-- equivalent up and an isomorphism, and hence, by univalence they are
-- consistent as equations.  The respective isomorphisms can be found
-- in products-thms.agda.
all-pred-append : ∀{X : Set}{f : X → Set}{l₁ l₂}
  → (p₁ : ∀{ℓ}{A : Set ℓ} → A ≡ (⊤ ∧ A))
  → (p₂ : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C))
  → all-pred f (l₁ ++ l₂) ≡ ((all-pred f l₁) ∧ (all-pred f l₂))
all-pred-append {l₁ = []} {l₂} p₁ p₂ = p₁
all-pred-append {X}{f}{x :: l₁} {l₂} p₁ p₂ rewrite all-pred-append {X}{f}{l₁ = l₁} {l₂} p₁ p₂ = p₂

map-proj-⊎₁ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 A) →
                proj-⊎₁ {A = A}{B} (map inj₁ l) ≡ l
map-proj-⊎₁ [] = refl
map-proj-⊎₁ {A = A}{B} (x :: l) rewrite map-proj-⊎₁ {A = A}{B} l = refl

map-proj-⊎₂ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 B) →
                proj-⊎₂ {A = A}{B} (map inj₂ l) ≡ l
map-proj-⊎₂ [] = refl
map-proj-⊎₂ {A = A}{B} (x :: l) rewrite map-proj-⊎₂ {A = A}{B} l = refl

map-proj-⊎₂-[] : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 A) →
                  proj-⊎₂ {A = A}{B} (map inj₁ l) ≡ []
map-proj-⊎₂-[] [] = refl
map-proj-⊎₂-[] {A = A}{B} (x :: l) rewrite map-proj-⊎₂-[] {A = A}{B} l = refl

map-proj-⊎₁-[] : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 B) →
                  proj-⊎₁ {A = A}{B} (map inj₂ l) ≡ []
map-proj-⊎₁-[] [] = refl
map-proj-⊎₁-[] {A = A}{B} (x :: l) rewrite map-proj-⊎₁-[] {A = A}{B} l = refl

is-empty-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → is-empty (l1 ++ l2) ≡ is-empty l1 && is-empty l2
is-empty-++ [] l2 = refl
is-empty-++ (x :: l1) l2 = refl

is-empty-ff-length : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → is-empty l ≡ ff → length l =ℕ 0 ≡ ff
is-empty-ff-length [] ()
is-empty-ff-length (x :: l) p = refl

--------------------------------------------------------
-- Exercises

-- 1. Which of the following formulas are theorems (i.e., they can be proved) about the list operations we have considered in this chapter?

-- (a) Can't be proved.

--++-sum : ∀ {ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → l1 ++ l2 ≡ l2 ++ l1
--++-sum [] l2 rewrite ++[] l2 = refl
--++-sum (x :: xs) l2 = ?
-- Goal: x :: xs ++ l2 ≡ l2 ++ x :: xs

-- (b) Can't be proved
--
-- Contradiction with length-map thm

-- (c) Can be proved

filter-repeat : ∀{ℓ}{A : Set ℓ}{p : A → 𝔹}{a : A}(n : ℕ) → p a ≡ ff → filter p (repeat n a) ≡ []
filter-repeat zero p = refl
filter-repeat (suc n) p rewrite p = filter-repeat n p

-- (d) Can't be proved. length-reverse thm contradicts this one.

-- ∀{ℓ}{A : Set ℓ}(l : 𝕃) → is-empty l ≡ tt → is-empty (reverse l) ≡ ff

-- (e) Can be proved.

filter-append : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l1 l2 : 𝕃 A) → filter p (l1 ++ l2) ≡ filter p l1 ++ filter p l2
filter-append p [] l2 = refl
filter-append p (x :: xs) l2 with p x
filter-append p (x :: xs) l2 | tt rewrite filter-append p xs l2 = refl
filter-append p (x :: xs) l2 | ff = filter-append p xs l2

-- 2. Indicate with typings listed will be accepted
--
-- (a) All but ii.

--test : 𝕃 𝕃
--test = []

-- (b) i (iv doesnt compile)

--test : ∀{ℓ}{A : Set ℓ} → (xs : 𝕃 A) → length xs
--test [] = 0
--test (x :: xs) = suc (test xs)

-- (c) i, ii,
--
-- v. "my-list-thms.agda|316 col 36 error|  𝕃 B should be a sort, but it isn't when checking that the expression A has type _865"

--test : ∀{ℓ}{A B C : Set ℓ} → (A → B → C) → 𝕃 A → 𝕃 (B → C)
--test : ∀{B : Set}{A : 𝕃 B} → (A → B) → (B → B) → 𝕃 A → 𝕃 B
--test f g x = map g (map f x)

-- 3. takeWhile

takeWhile : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
takeWhile p [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

-- 4. prove it

takeWhile-repeat : ∀{ℓ}{A : Set ℓ}{p : A → 𝔹}{a : A}(n : ℕ) → p a ≡ tt → takeWhile p (repeat n a) ≡ repeat n a
takeWhile-repeat zero p = refl
takeWhile-repeat{p = p₁}(suc n) p rewrite p | takeWhile-repeat{p = p₁} n p = refl
-- Goal: if p₁ a then a :: takeWhile p₁ (repeat n a) else [] ≡ a :: repeat n a
-- Goal: a :: takeWhile p₁ (repeat n a) ≡ a :: repeat n a
-- Goal: a :: repeat n a ≡ a :: repeat n a
--
-- The type annotation is required.

-- 5. take

take : ∀{ℓ}{A : Set ℓ}(n : ℕ) → 𝕃 A → 𝕃 A
take zero xs = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs

-- 6.

take-nthTail : ∀{ℓ}{A : Set ℓ}(n : ℕ)(l : 𝕃 A) → take n l ++ nthTail n l ≡ l
take-nthTail zero l = refl
take-nthTail (suc n) [] = refl
take-nthTail (suc n) (x :: xs) rewrite take-nthTail n xs = refl
-- Goal: x :: take n xs ++ nthTail n xs ≡ x :: xs
--       x :: xs ≡ x :: xs
