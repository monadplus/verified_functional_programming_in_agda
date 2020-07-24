module exercises where

open import my-bool hiding (_xor_)

infix 6 _xor_

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor tt = ff
tt xor ff = tt
ff xor tt = tt
ff xor ff = ff

data day : Set where
  Monday : day
  Tuesday : day
  Wednesday : day
  Thursday : day
  Friday : day
  Saturday : day
  Sunday : day

nextday_ : day → day
nextday Monday = Tuesday
nextday Tuesday = Wednesday
nextday Wednesday = Thursday
nextday Thursday = Friday
nextday Friday = Saturday
nextday Saturday = Sunday
nextday Sunday = Monday

data suit : Set where
  hearts : suit
  spades : suit
  diamonds : suit
  clubs : suit

is-red_ : suit -> 𝔹
is-red hearts = tt
is-red diamonds = tt
is-red _ = ff
