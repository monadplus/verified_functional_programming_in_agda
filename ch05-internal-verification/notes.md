# Chapter 5: Internal Verification

We wrote some operations (booleans, natural numbers, lists) and wrote some proofs of properties of those operations.

This style of verification in type theory is called **external verification**: proofs are external to programs i.e. proofs are distinct artifacts one writes about some pre-existing programs.

**internal verification**: alternative style of type-theoretic verification. The idea is to write functions with more semantically expressive types. Example vector.

We will see several examples of internal verification in this chapter:

- vectors (statically enforce the length)
- braum trees (statically enforce the balancing property)
- BSTs
- Sigma Types
