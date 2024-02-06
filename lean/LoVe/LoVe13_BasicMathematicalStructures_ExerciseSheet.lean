/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe Exercise 13: Basic Mathematical Structures

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Type Classes

Recall the inductive type `BinTree` we introduced in lecture 5: -/

#check BinTree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def BinTree.graft {α : Type} : BinTree α → BinTree α → BinTree α
  | BinTree.empty,      u => u
  | BinTree.node a l r, u =>
    BinTree.node a (BinTree.graft l u) (BinTree.graft r u)

#reduce BinTree.graft (BinTree.node 1 BinTree.empty BinTree.empty)
  (BinTree.node 2 BinTree.empty BinTree.empty)

/- 1.1. Prove the following two theorems by structural induction on `t`. -/

theorem BinTree.graft_assoc {α : Type} (t u v : BinTree α) :
  BinTree.graft (BinTree.graft t u) v = BinTree.graft t (BinTree.graft u v) :=
  sorry

theorem BinTree.graft_empty {α : Type} (t : BinTree α) :
  BinTree.graft t BinTree.empty = t :=
  sorry

/- 1.2. Declare `BinTree` an instance of `AddMonoid` using `graft` as the
addition operator. -/

#print AddMonoid

@[instance] def BinTree.AddMonoid {α : Type} : AddMonoid (BinTree α) :=
  { add       :=
      sorry
    add_assoc :=
      sorry
    zero      :=
      sorry
    add_zero  :=
      sorry
    zero_add  :=
      sorry
  }

/- 1.3 (**optional**). Explain why `BinTree` with `graft` as addition cannot
be declared an instance of `AddGroup`. -/

#print AddGroup

-- enter your explanation here

/- 1.4 (**optional**). Prove the following theorem illustrating why `BinTree`
with `graft` as addition does not constitute an `AddGroup`. -/

theorem BinTree.add_left_neg_counterexample :
  ∃x : BinTree ℕ, ∀y : BinTree ℕ, BinTree.graft y x ≠ BinTree.empty :=
  sorry


/- ## Question 2: Multisets and Finsets

Recall the following definitions from the lecture: -/

#check Finset.elems
#check List.elems

/- 2.1. Prove that the finite set of nodes does not change when mirroring a
tree. -/

theorem Finset.elems_mirror (t : BinTree ℕ) :
  Finset.elems (mirror t) = Finset.elems t :=
  sorry

/- 2.2. Show that this does not hold for the list of nodes by providing a
tree `t` for which `List.elems t ≠ List.elems (mirror t)`.

If you define a suitable counterexample, the proof below will succeed. -/

def rottenTree : BinTree ℕ :=
  sorry

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
  ∃t : BinTree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe
