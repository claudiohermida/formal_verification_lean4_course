---- Bool

def negate (b : Bool) : Bool :=
  match b with
  | true  => false
  | false => true

#eval (negate true)

-- 1. Implement functions `and`, `or`, and `xor` for values of type `Bool`.

namespace bool

def and (b1 : Bool) (b2 : Bool) : Bool :=
  match b1, b2 with
  | true, true => true
  | _, _ => false

#eval (and true true)
#eval (and true false)
#eval (and false true)
#eval (and false false)

def or (b1 : Bool) (b2 : Bool) : Bool :=
  match b1, b2 with
  | _, true => true
  | true, _ => true
  | _, _ => false

#eval (or true true)
#eval (or true false)
#eval (or false true)
#eval (or false false)

def xor (b1 : Bool) (b2 : Bool) : Bool :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, true => true
  | _, _ => false

#eval (xor true true)
#eval (xor true false)
#eval (xor false true)
#eval (xor false false)

end bool

-- 2. Write a function `upper` which takes a `Person` and returns a `Person` where the `name` is changed to uppercase.

structure Person where
  id : Nat
  name : String

def upper (P: Person): Person :=
 {P with name := String.toUpper (P.name)}

def Claudio: Person := {id := 1, name := "Claudio"}

#eval upper Claudio


-- 3. Implement a simple instance of `BEq` for `Direction` and implement separate instances of `Ord` for `Person`, numerically and lexicographically.

inductive Direction where
  | north
  | south
  | west
  | east

instance : BEq Direction where
  beq dₐ1 dₐ2 :=
    match dₐ1, dₐ2 with
    | Direction.north, Direction.north => true
    | Direction.south, Direction.south => true
    | Direction.west, Direction.west => true
    | Direction.east, Direction.east => true
    | _, _ => false

  #eval (BEq.beq Direction.north Direction.north)
  #eval (BEq.beq Direction.north Direction.south)
  #eval (BEq.beq Direction.north Direction.west)
  #eval (BEq.beq Direction.north Direction.east)
  #eval (BEq.beq Direction.south Direction.north)
  #eval (BEq.beq Direction.south Direction.south)
  #eval (BEq.beq Direction.south Direction.west)
  #eval (BEq.beq Direction.south Direction.east)
  #eval (BEq.beq Direction.west Direction.north)
  #eval (BEq.beq Direction.west Direction.south)


-- 4. Find out and interpret the type signatures of the terms `[]`, `Just`, `Right`. Which syntactic/semantic features in Lean make parametric polymorphism more clearer/rigorous compared to Haskell?

#check []
#check Option.some
#check Or.inr


-- 5. Write a function which filters a `List Nat` based on a given predicate? Why is `filter` easy to define but not `factorial` which seems more trivial?

def natFilter (l: List Nat) (f: Nat -> Bool) : List Nat :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: natFilter xs f else natFilter xs f


-- here the recursive case applies natFilter to xs, which is a subterm of the argument x :: xs, hence it is 'decreasing in complexity

-- 6. Complete the implementation of `creditAccount` and `transferFunds` in the Ledger model.

abbrev Ident := Nat
abbrev Amount := Nat

structure Account where
  id : Ident
  name : String
  bal : Amount
  deriving Repr

abbrev Ledger := List Account

def creditAccount (l: Ledger) (id:  Ident) (amt: Amount) : Option
Ledger :=
match l with
| [] => none
| h :: t => if (h.id == id) then
          some ({ h with bal := h.bal + amt } :: t)
      else Functor.map (fun t' => h :: t') (creditAccount t id amt)


def debitAccount (l: Ledger) (id: Ident) (amt: Amount) : Option Ledger :=
  match l with
  | [] => none
  | h :: t =>
    if h.id == id then
      if h.bal >= amt then
        some ({ h with bal := h.bal - amt } :: t)
      else
        none
    else
      Functor.map (fun t' => h :: t') (debitAccount t id amt)

def transferFunds (l : Ledger) (fromId : Ident) (toId : Ident) (amt : Amount) : Option Ledger :=
  match debitAccount l fromId amt with
  | none => none
  | some l' => creditAccount l' toId amt
