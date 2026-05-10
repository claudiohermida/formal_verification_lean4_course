
import Mathlib.Tactic
import Blaster

abbrev Ident := Nat
abbrev Amount := Nat

structure Account where
  id : Ident
  name : String
  bal : Amount
  deriving Repr, BEq, DecidableEq

abbrev Ledger := List Account

def Alice: Account := {
  id   := 1,
  name := "Alice",
  bal  := 1000
}

def Bob: Account := {
  id   := 2,
  name := "Bob",
  bal  := 200
}

def Charlie: Account := {
  id   := 3,
  name := "Charlie",
  bal  := 500
}

def Dave : Account := {
  id   := 4,
  name := "Dave",
  bal  := 1000
}

def addAccount (l : Ledger) (a : Account) : Ledger :=
  if l.any (fun x => x.id == a.id)
  then l
  else a :: l


def testLedger : Ledger := addAccount (addAccount (addAccount [] Alice) Bob) Charlie

#eval testLedger

#eval addAccount testLedger Dave
#eval addAccount testLedger Bob


theorem addAccount_length (l : Ledger) (a : Account) :
  (addAccount l a).length = l.length ∨ (addAccount l a).length = l.length + 1
  := by
  unfold addAccount
  split <;> simp

theorem addAccount_exists (l : Ledger) (a : Account) :
  a ∈ l -> (addAccount l a).length = l.length := by
  intro a_in_l
  unfold addAccount
  split_ifs with if_any
  next => rfl
  next =>
    have if_any_contra : List.any l (λ x => x.id == a.id) = true := by
      simp [List.any_eq_true]
      use a
    contradiction


theorem addAccount_not_exists (l : Ledger) (a : Account) :
  ¬ (l.any (λ x => x.id == a.id) = true) -> (addAccount l a).length = l.length + 1 := by -- sorry
      unfold addAccount
      intro hacc_nexist
      simp [hacc_nexist]




theorem addAccount_idem (l : Ledger) (a : Account) :
  addAccount (addAccount l a) a = addAccount l a := by
  unfold addAccount
  split <;> simp





def getBalance (l : Ledger) (id : Ident) : Option Amount :=
(l.find? (λ x => x.id == id)).map (λ x => x.bal)

#eval getBalance testLedger 1
#eval getBalance testLedger 5


def getSupply (l : Ledger) : Amount := -- sorry
(l.map (λ x => x.bal)).sum

#eval getSupply testLedger




def debitAccount (l : Ledger) (id : Ident) (amt : Amount) : Option Ledger :=
  match l with
  | [] => none
  | h :: t =>
    if (h.id == id) then
      if (h.bal >= amt) then
        some ({ h with bal := h.bal - amt } :: t)
      else none
    else Functor.map (fun t' => h :: t') (debitAccount t id amt)

#eval debitAccount testLedger 1 100
#eval debitAccount testLedger 1 1100


def creditAccount (l : Ledger) (id : Ident)  (amt : Amount) : Option Ledger := -- sorry
match l with
| [] => none
| h :: t =>
  if (h.id == id) then
    some ({ h with bal := h.bal + amt } :: t)
  else Functor.map (fun t' => h :: t') (creditAccount t id amt)

#eval creditAccount testLedger 3 100
#eval creditAccount testLedger 5 100


def transferFunds (l : Ledger) (fromId : Ident) (toId : Ident) (amt : Amount) : Option Ledger :=
  match debitAccount l fromId amt with
  | none => none
  | some l' => creditAccount l' toId amt

#eval transferFunds testLedger 1 1 100
#eval transferFunds testLedger 3 1 10
#eval transferFunds testLedger 3 5 100
