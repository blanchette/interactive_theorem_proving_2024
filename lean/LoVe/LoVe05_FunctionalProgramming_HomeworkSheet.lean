/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe Homework 5 (10 points + 2 bonus points): Functional Programming

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Huffman Trees

Consider the following type of weighted binary trees: -/

inductive HTree (α : Type)
  | leaf  : ℕ → α → HTree α
  | inner : ℕ → HTree α → HTree α → HTree α

/- Each constructor corresponds to a kind of node. An `HTree.leaf` node stores a
numeric weight and a label of some type `α`, and an `HTree.inner` node stores a
numeric weight, a left subtree, and a right subtree.

1.1 (1 point). Define a polymorphic Lean function called `weight` that takes a
tree over some type variable `α` and that returns the weight component of the
root node of the tree: -/

def weight {α : Type} : HTree α → ℕ :=
  sorry

/- 1.2 (1 point). Define a polymorphic Lean function called `unite` that takes
two trees `l, r : HTree α` and that returns a new tree such that (1) its left
child is `l`; (2) its right child is `r`; and (3) its weight is the sum of the
weights of `l` and `r`. -/

def unite {α : Type} : HTree α → HTree α → HTree α :=
  sorry

/- 1.3 (2 points). Consider the following `insort` function, which inserts a
tree `u` in a list of trees that is sorted by increasing weight and which
preserves the sorting. (If the input list is not sorted, the result is not
necessarily sorted.) -/

def insort {α : Type} (u : HTree α) : List (HTree α) → List (HTree α)
  | []      => [u]
  | t :: ts => if weight u ≤ weight t then u :: t :: ts else t :: insort u ts

/- Prove that `insort`ing a tree into a list cannot yield the empty list: -/

theorem insort_Neq_nil {α : Type} (t : HTree α) :
  ∀ts : List (HTree α), insort t ts ≠ [] :=
  sorry

/- 1.4 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

-- enter your paper proof here


/- ## Question 2 (4 points + 2 bonus points): Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 2.1 (2 points). Prove the following theorem, discovered by Carl Friedrich
Gauss as a pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic introduced in lecture 6 might be useful to reason about
  addition. -/

/- PAUL: I can't see any reference to `linarith` in the file. Is this something you
         mention in the lecture but not the demo file? It would be worth summarising
         what it is, or referring to the Guide.
         Actually, I just looked ahead, there is a comment in chapter 6. Maybe copy to here? -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
  ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1) :=
  sorry

/- 2.2 (2 points). Prove the following property of `sumUpToOfFun`. -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
    sumUpToOfFun f n + sumUpToOfFun g n :=
  sorry

/- 2.3 (2 bonus points). Prove `sumUpToOfFun_mul` again as a "paper" proof.
Follow the guidelines given in question 1.4 of the exercise. -/

-- enter your paper proof here

end LoVe
