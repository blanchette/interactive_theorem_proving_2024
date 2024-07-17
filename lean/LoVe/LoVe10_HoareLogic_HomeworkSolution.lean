/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_ExerciseSheet
import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Homework 10 (10 points + 1 bonus point): Hoare Logic

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): Factorial

The following WHILE program is intended to compute the factorial of `n₀`, leaving
the result in `r`. -/

def FACT : Stmt :=
  Stmt.assign "i" (fun s ↦ 0);
  Stmt.assign "r" (fun s ↦ 1);
  Stmt.whileDo (fun s ↦ s "i" ≠ s "n")
    (Stmt.assign "i" (fun s ↦ s "i" + 1);
     Stmt.assign "r" (fun s ↦ s "r" * s "i"))

/- Recall the definition of the `fact` function: -/

#print fact

/- Let us register its recursive equations as simplification rules to
strengthen the simplifier and `aesop`, using some new Lean syntax: -/

attribute [simp] fact

/- Prove the correctness of `FACT` using `vcg`.

Hint: Remember to strengthen the loop invariant with `s "n" = n₀` to
capture the fact that the variable `n` does not change. -/

theorem FACT_correct (n₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ *} (FACT) {* fun s ↦ s "r" = fact n₀ *} :=
show {* fun s ↦ s "n" = n₀ *}
     (Stmt.assign "i" (fun s ↦ 0);
      Stmt.assign "r" (fun s ↦ 1);
      Stmt.invWhileDo
        (fun s ↦ s "r" = fact (s "i") ∧ s "n" = n₀)
        (fun s ↦ s "i" ≠ s "n")
        (Stmt.assign "i" (fun s ↦ s "i" + 1);
         Stmt.assign "r" (fun s ↦ s "r" * s "i")))
     {* fun s ↦ s "r" = fact n₀ *} from
  by
    vcg <;>
      aesop <;>
      ac_rfl


/- ## Question 2 (5 points + 1 bonus point):
## Hoare Logic for the Guarded Command Language

Recall the definition of GCL from exercise 9: -/

namespace GCL

#check Stmt
#check BigStep

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro (priority := high) "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" :
  term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

/- 2.1 (5 points). Prove the following Hoare rules: -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
    (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} :=
  by
    intro s t hs hst
    apply hq
    apply h
    { apply hp
      assumption }
    { assumption }

theorem assign_intro {P x a} :
  {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
    intros s t hp hst
    cases hst
    assumption

theorem assert_intro {P Q : State → Prop} :
  {* fun s ↦ Q s → P s *} (Stmt.assert Q) {* P *} :=
  by
    intros s t hs hst
    cases hst with
    | assert _ _ hB => exact hs hB

theorem seq_intro {P Q R S T}
  (hS : {* P *} (S) {* Q *}) (hT : {* Q *} (T) {* R *}) :
  {* P *} (Stmt.seq S T) {* R *} :=
  by
    intro s t hp hst
    aesop

theorem choice_intro {P Q Ss}
    (h : ∀i (hi : i < List.length Ss), {* P *} (Ss[i]'hi) {* Q *}) :
  {* P *} (Stmt.choice Ss) {* Q *} :=
  by
    intro s t hs hst
    aesop

/- 2.2 (1 bonus point). Prove the rule for `loop`. Notice the similarity with
the rule for `while` in the WHILE language. -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
  {* P *} (Stmt.loop S) {* P *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.loop S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | assign    => cases ws_eq
    | assert    => cases ws_eq
    | seq       => cases ws_eq
    | choice    => cases ws_eq
    | loop_base =>
      cases ws_eq
      assumption
    | loop_step =>
      cases ws_eq
      aesop

end PartialHoare

end GCL

end LoVe
