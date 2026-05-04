inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

open Natural

def x : Natural := zero
def y : Natural := succ zero

def add x y := match x with
  | zero   => y
  | succ z => succ (add z y)

def mult (x y : Nat) : Nat := sorry

def factorial (x : Nat) : Nat := sorry
