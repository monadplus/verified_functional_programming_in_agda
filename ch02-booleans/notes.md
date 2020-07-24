Constructive Logic vs Classic Logic

Constructive Logic do not inclue the law of the excluded middle and double negation elimination, which are fundamental inference rules in classic logic.

(Law of excluded middle: for every formula F, F \/ neg F)

Example of law of the excluded middle:

Theorem 2.1.1 (Hindley). There exist irrational numbers a and b such that a^b is rational.

Proof (pg. 29) Uses the law of the excluded middle.

Theorem 2.1.2 (Constructive version). There exist irrational numbers a and b such that a^b is rational.

Proof. (pg. 30)

Theorem 2.1.3. Either the sum \pi + \e  or the product \pi\e (or both) is irrational.

The proof is nonconstructive.

It does not appear possible to use the Curry-Howard isomorphism with nonconstructive reasoning.

For it seems that a program that proves \forall F. F \/ \neg F would have to be a universal oracle, which given any formula F coul dcompute whether F is true or else report that F is false. So if one wanted to know if the Goldbach Conjecture (which states that every sinteger greater than two is the sum of two prime numbers) is true or false, one could just ask this oracle.

The Curry-Howard isomorphism can be made to work for classical logic (timothy Griffin, and still an active subject of research) (more on the book).


