/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
  Odd 1 :=
  by
    intro ho1
    cases ho1

/- 1.2. Prove that 3 and 5 are odd. -/

theorem Odd_3 :
  Odd 3 :=
  by
    intro ho3
    cases ho3 with
    | add_two _ ho1 =>
      cases ho1

theorem odd_5 :
  Odd 5 :=
  by
    intro ho5
    cases ho5 with
    | add_two _ ho3 =>
      cases ho3 with
      | add_two _ ho1 =>
        cases ho1

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
  ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 =>
    by
      apply Even.add_two
      simp
      apply Even_two_times


/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  | vs {m n : ℕ} : m > n → ServAhead (Score.vs m n)
  | adv_serv     : ServAhead Score.advServ
  | game_serv    : ServAhead Score.gameServ

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
  ServAhead (Score.vs m n) :=
  ServAhead.vs hgt

theorem ServAhead_advServ :
  ServAhead Score.advServ :=
  ServAhead.adv_serv

theorem not_ServAhead_advRecv :
  ¬ ServAhead Score.advRecv :=
  by
    intro h
    cases h

theorem ServAhead_gameServ :
  ServAhead Score.gameServ :=
  ServAhead.game_serv

theorem not_ServAhead_gameRecv :
  ¬ ServAhead Score.gameRecv :=
  by
    intro h
    cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

/- The positive theorems correspond exactly to the introduction rules of the
definition. By contrast, the negative theorems have no counterparts in the
definition. -/


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
  ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  by
    intro t fmt
    have fmmt : IsFull (mirror (mirror t)) :=
      IsFull_mirror _ fmt
    rw [mirror_mirror] at fmmt
    assumption

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node (f a) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil
  | Tree.nil        => by simp [Tree.map]
  | Tree.node _ _ _ => by simp [Tree.map]

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_mirror {α β : Type} (f : α → β) :
  ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  by
    intro t hfull
    induction hfull with
    | nil =>
      simp [Tree.map]
      exact IsFull.nil
    | node a l r hl hr hiff ihl ihr =>
      simp [Tree.map]
      apply IsFull.node
      { exact ihl }
      { exact ihr }
      { simp [Tree.map_eq_empty_iff]
        assumption }

end LoVe
