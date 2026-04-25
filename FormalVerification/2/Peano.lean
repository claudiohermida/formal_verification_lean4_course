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
def factorial (x : Natural) : Natural := sorry
