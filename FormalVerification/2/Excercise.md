Session 2: Exercises
====================

1. Define `mult : Nat -> Nat -> Nat` and `factorial : Nat -> Nat` for `Natural` numbers.

2. Translate the following logical statements into types using Curry–Howard correspondence:
    - `P /\ (Q \/ R)`
    - `(P -> Q) -> R`
    - `~ ~ ~ P`
3. Is a function of type `False -> P` possible  for any `P`. Why? What does this fact correspond to in logic?

4. Try to prove the following propositions using principle induction: 
    - `forall n : Nat. n = n + 0`
    - `forall x y : String. length (x ++ y) = length x + length y`