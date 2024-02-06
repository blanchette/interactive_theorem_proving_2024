/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Homework 12 (10 points + 2 bonus points):
# Logical Foundations of Mathematics

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (8 points): Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `Even n` to our
theorem statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1 (1 point). Define the type `Eveℕ` of even natural numbers, using the `Even`
predicate introduced in the lecture 5 demo. -/

#print Even

def Eveℕ : Type :=
  sorry

/- 1.2 (1 point). Prove the following theorem about the `Even` predicate. You will
need it to answer question 1.3.

Hint: The theorems `add_assoc` and `add_comm` might be useful. -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
  Even (m + n) :=
  sorry

/- 1.3 (2 points). Define zero and addition of even numbers by filling in the
`sorry` placeholders. -/

def Eveℕ.zero : Eveℕ :=
  sorry

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  sorry

/- 1.4 (4 points). Prove that addition of even numbers is commutative and
associative, and has 0 as an identity element. -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
  Eveℕ.add m n = Eveℕ.add n m :=
  sorry

theorem Eveℕ.add_assoc (l m n : Eveℕ) :
  Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  sorry

theorem Eveℕ.add_iden_left (n : Eveℕ) :
  Eveℕ.add Eveℕ.zero n = n :=
  sorry

theorem Eveℕ.add_iden_right (n : Eveℕ) :
  Eveℕ.add n Eveℕ.zero = n :=
  sorry


/- ## Question 2 (2 points + 2 bonus points): Hilbert Choice

2.1 (2 bonus points). Prove the following theorem.

Hints:

* A good way to start is to make a case distinction on whether `∃n, f n < x`
  is true or false.

* The theorem `le_of_not_gt` might be useful. -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
  ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
| x, m, eq =>
  by
    sorry, sorry

/- Now this interesting theorem falls off: -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
  ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 2.2 (1 point). Use what you learned about Hilbert choice in the lecture to
define the following function, which returns the (or an) index of the minimal
element in `f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  sorry

/- 2.3 (1 point). Prove the following characteristic theorem about your
definition. -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
  ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  sorry

end LoVe
