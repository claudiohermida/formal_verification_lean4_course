

/- 1. Given `P Q R : Prop`, prove the following theorems:
  - `P ∧ Q -> Q ∧ P`
  - ` P ∨ Q -> (¬ P) -> Q`
  - `P ∨ Q -> (P -> R) -> (Q -> R) -> R`
-/

theorem my_and_comm (P Q : Prop) : P ∧ Q -> Q ∧ P :=
  fun hpq => And.intro hpq.right hpq.left
-- Alternatively: fun ⟨hp, hq⟩ => ⟨hq, hp⟩

theorem my_or_neg (P Q: Prop) : P ∨ Q -> (¬ P) -> Q :=
fun hp_q hnp =>
  Or.elim hp_q
    (fun hp => absurd hp hnp)
    (fun hq => hq)

-- alternatively
theorem my_or_neg_q (P Q : Prop) : P ∨ Q -> (¬ P) -> Q :=
  fun h hnp => h.elim (fun hp => absurd hp hnp) (fun hq => hq)

theorem my_or_elim (P Q R : Prop) : P ∨ Q -> (P -> R) -> (Q -> R) -> R :=
  fun hp_q hpTor hqTor =>
      hp_q.elim
        (fun hp => hpTor hp)
        (fun hq => hqTor hq)


-- alternatively
theorem my_or_resolve (P Q R : Prop) : P ∨ Q -> (P -> R) -> (Q -> R) -> R :=
  fun h hpr hqr => h.elim hpr hqr

theorem my_or_resolve_tactic (P Q R : Prop) : P ∨ Q -> (P -> R) -> (Q -> R) -> R := by
  intro hp_q hpTor hqTor
  cases hp_q with
  | inl hp => exact hpTor hp
  | inr hq => exact hqTor hq
-- End of theorem 1

/- 2. Given `P Q R : Prop`, prove the De Morgan Law (you may need `Classical.em` in one of these):
  - `¬ (P ∧ Q) <-> ¬ P ∨ ¬ Q`
  - `¬ (P ∨ Q) <-> ¬ P ∧ ¬ Q`
-/

open Classical

theorem my_de_morgan_and (P Q : Prop) : ¬ (P ∧ Q) <-> ¬ P ∨ ¬ Q :=
have lem := Classical.em P
Iff.intro
  (fun hnp_and_q => lem.elim
     (fun hp => Or.inr (fun hq => hnp_and_q ⟨hp, hq⟩))
     (fun hnp => Or.inl hnp)
  )
  (fun hnp_or_nq => hnp_or_nq.elim
      (fun hnp => (fun hp_and_q => absurd hp_and_q.left hnp))
      (fun hnq => (fun hp_and_q => absurd hp_and_q.right hnq))
  )

theorem my_de_morgan_or (P Q : Prop) : ¬ (P ∨ Q) <-> ¬ P ∧ ¬ Q :=
Iff.intro
 ( fun hnp_or_q =>
      And.intro
        (fun hp => absurd (Or.inl hp) hnp_or_q)
        (fun hq => absurd (Or.inr hq) hnp_or_q)
  )
  (fun hnp_and_nq => (fun hp_or_q => hp_or_q.elim
      (fun hp => absurd hp hnp_and_nq.left)
      (fun hq => absurd hq hnp_and_nq.right)
      )
  )

-- end theorem 2

/- 3. Given `a b c : Nat`, prove the following theorems:
  - `a + 1 = 1 + a`
  - `a * 0 = 0`
  - `a * b = b * a`
  - `a * (b + c) = a * b + a * c`
-/

namespace excercise_3

variable (a b c : Nat)

theorem add_1_comm (a : Nat) : a + 1 = 1 + a := by
induction a with
| zero => rfl
| succ n ih =>
  have h : 1 + (n + 1) = (1 + n) + 1 := by exact (Nat.add_assoc 1 n 1)
  rw [h]
  rw [ih]

theorem mult_zero (a b : Nat) : a * 0 = 0 := by
induction a with
| zero => rfl
| succ n ih =>
  simp [Nat.succ_mul, ih]

theorem mult_comm (a b c : Nat) : a * b = b * a := by
induction a with
| zero => simp
| succ n ih =>
  simp [Nat.succ_mul, ih, Nat.mul_succ]

theorem mult_left_distrib (a b c : Nat) : a * (b + c) = a * b + a * c := by
induction a with
| zero => simp
| succ n ih =>
  simp [Nat.succ_mul, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end excercise_3




/- 4. Given `a b : Bool`, prove the following theorems:
  - `a && b = b && a`
  - `not (not a) = a`
  - `not (a || b) = not a && not b`
-/

theorem bool_and_comm (a b : Bool) : a && b = b && a := by
  cases a <;> cases b <;> simp

theorem my_and_eq_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem my_double_neg (a  : Bool) : not (not a) = a := by
  cases a <;> simp

theorem my_not_distr_or (a b : Bool) : not (a || b) = not a && not b := by
  cases a <;> cases b <;> simp





/- 5. Given `x y : List α`, prove the following theorems...
  - `(x ++ y).length = x.length + y.length`
  - `(reverse x).length = x.length`
  - `x.reverse.reverse = x`
-/


namespace Lists

variable (x y : List α)

theorem length_concat (x y : List α) : (x ++ y).length = x.length + y.length := by
induction x with
  | nil => simp
  | cons h t ih =>
      calc
        (h::t ++ y).length = (h::(t++ y)).length := by rw [List.cons_append]
                      _    = (t ++ y).length + 1 := by rw [List.length_cons]
                      _    = (t.length + y.length) + 1 := by rw [ih]
                      _    = (t.length + 1) + y.length := by rw [Nat.add_assoc t.length y.length 1, Nat.add_comm y.length 1, ← Nat.add_assoc t.length 1 y.length]
                      _    =  (h::t).length + y.length := by rw [List.length_cons]



theorem my_reverse_length (x : List α) : (List.reverse x).length = x.length := by
induction x with
  | nil => rfl
  | cons h t ih =>
        calc
          (List.reverse (h::t)).length = (List.reverse t ++ [h]).length  := by rw [List.reverse_cons]
          _                            = (List.reverse t).length + [h].length := by rw [length_concat (List.reverse t) [h]]
          _                            = t.length + [h].length := by rw [ih]
          _                            = t.length + 1 := rfl
          _                            = (h::t).length := by rw [List.length_cons]

theorem my_reverse_reverse (x : List α) : x.reverse.reverse = x := by
induction x with
  | nil => rfl
  | cons h t ih =>
      calc
        (List.reverse (List.reverse (h::t))) = List.reverse (List.reverse t ++ [h])              := by rw [List.reverse_cons]
        _                                    = List.reverse [h] ++ List.reverse (List.reverse t) := by rw [List.reverse_append]
        _                                    = [h] ++ List.reverse (List.reverse t)              := by rfl
        _                                    = [h] ++ t                                          := by rw [ih]
        _                                    = h::t                                              := by rfl

end Lists
