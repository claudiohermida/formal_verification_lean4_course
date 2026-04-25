import Std

/- 1. Define `mult : Nat -> Nat -> Nat` and `factorial : Nat -> Nat` for `Natural` numbers.
-/

inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

open Natural

def z : Natural := zero
def one : Natural := succ zero
def two : Natural := succ one
def three : Natural := succ two
def four : Natural := succ three

def add x y := match x with
  | zero   => y
  | succ z => succ (add z y)


-- excercise
def mult (x y : Natural) : Natural := match x with
  | zero => zero
  | succ z => add (mult z y) y


#eval mult two two


-- excercise
def factorial (x : Natural) : Natural := match x with
  | zero => one
  | succ y => mult (succ y) (factorial y)

#eval factorial three


/- 2. Translate the following logical statements into types using Curry–Howard correspondence:
    - `P /\ (Q \/ R)`. <==> P × (Q ⊗ R). <==> P ∧ (Q ∨ R)
    - `(P -> Q) -> R`. <==> (P → (Q → R))

    - `~ ~ ~ P` <--> ¬ ¬ ¬ P <==> ((P → ⊥) → ⊥) → ⊥
-/

/- theorem my_and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.right, h.left⟩
-/

/- 3. Is a function of type `False -> P` possible  for any `P`. Why? What does this fact correspond to in logic?
ANSWER: Yes, it is possible. "Ex Falso Quodlibet" From falsehood, everything follows. In Lean, it is "False.elim"
-/


/-  4. Try to prove the following propositions using principle induction:
    - `forall n : Nat. n = n + 0`
    - `forall x y : String. length (x ++ y) = length x + length y`
-/


def add_zero_term : ∀ (n : Nat), n = n + 0
  | 0      => rfl
  | (n + 1) =>
    -- We use 'congrArg' to apply 'succ' to both sides of the IH
    congrArg Nat.succ (add_zero_term n)





theorem my_add_zero_term : ∀ (n : Natural), n = add n zero := by
  intro n
  induction n with
  | zero => rfl
  | succ y ih =>
    calc
      succ y = succ (add y zero) := congrArg succ ih
      _      = add (succ y) zero := rfl

open Std

theorem length_distributivity (x y : String) : String.length (x ++ y) = String.length x + String.length y := by
  -- Bridge the String definitions to List operations
  -- String.length s = s.data.length
  -- (x ++ y).data = x.data ++ y.data
  show (x.data ++ y.data).length = x.data.length + y.data.length
  let yl := y.data
  induction x.data with
  | nil =>
    calc
      ([] ++ yl).length = yl.length := rfl
      _ = 0 + yl.length := by rw [Nat.zero_add]
  | cons h t ih =>
    calc
      ((h :: t) ++ yl).length
      = (h :: (t ++ yl)).length := rfl
      _ = (t ++ yl).length + 1 := rfl
      _ = (t.length + yl.length) + 1 := by rw [ih]
      _ = (t.length + 1) + yl.length := by rw [Nat.add_right_comm]
