/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 9 (10 points + 1 bonus point): Operational Semantics

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): Arithmetic Expressions

Recall the type of arithmetic expressions from lecture 1 and its evaluation
function: -/

#check AExp
#check eval

/- Let us introduce the following abbreviation for an environment that maps
variable names to values: -/

def Envir : Type :=
  String → ℤ

/- 1.1 (2 points). Complete the following Lean definition of a big-step-style
semantics for arithmetic expressions. The predicate `BigStep` (`⟹`) relates
an arithmetic expression, an environment, and the value to which the expression
evaluates in the given environment: -/

inductive BigStep : AExp × Envir → ℤ → Prop
  | num (i env) : BigStep (AExp.num i, env) i
  | var (x env) : BigStep (AExp.var x, env) (env x)
  | add (a₁ a₂ i₁ i₂ env) :
    BigStep (a₁, env) i₁ → BigStep (a₂, env) i₂ →
    BigStep (AExp.add a₁ a₂, env) (i₁ + i₂)
  | sub (a₁ a₂ i₁ i₂ env) :
    BigStep (a₁, env) i₁ → BigStep (a₂, env) i₂ →
    BigStep (AExp.sub a₁ a₂, env) (i₁ - i₂)
  | mul (a₁ a₂ i₁ i₂ env) :
    BigStep (a₁, env) i₁ → BigStep (a₂, env) i₂ →
    BigStep (AExp.mul a₁ a₂, env) (i₁ * i₂)
  | div (a₁ a₂ i₁ i₂ env) :
    BigStep (a₁, env) i₁ → BigStep (a₂, env) i₂ →
    BigStep (AExp.div a₁ a₂, env) (i₁ / i₂)

infix:60 " ⟹ " => BigStep

/- 1.2 (1 point). Prove the following theorem to validate your definition
above.

Hint: It may help to first prove
`(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2`. -/

theorem BigStep_add_two_two (env : Envir) :
  (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 :=
  by
    apply BigStep.add _ _ 2 2 <;>
      apply BigStep.num

/- 1.3 (2 points). Prove that the big-step semantics is sound with respect to
the `eval` function: -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
  eval (Prod.snd aenv) (Prod.fst aenv) = i :=
  by
    induction hstep with
    | num i env                         => rfl
    | var x env                         => rfl
    | add a₁ a₂ i₁ i₂ env h₁ h₂ ih₁ ih₂ =>
        simp at *
        simp [eval, *]
    | sub a₁ a₂ i₁ i₂ env h₁ h₂ ih₁ ih₂ =>
      simp at *
      simp [eval, *]
    | mul a₁ a₂ i₁ i₂ env h₁ h₂ ih₁ ih₂ =>
      simp at *
      simp [eval, *]
    | div a₁ a₂ i₁ i₂ env h₁ h₂ ih₁ ih₂ =>
      simp at *
      simp [eval, *]


/- ## Question 2 (5 points + 1 bonus point): Semantics of Regular Expressions

Regular expressions are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `Regex` to represent the following grammar:

    R  ::=  ∅       -- `nothing`: matches nothing
         |  ε       -- `empty`: matches the empty string
         |  a       -- `atom`: matches the atom `a`
         |  R ⬝ R    -- `concat`: matches the concatenation of two regexes
         |  R + R   -- `alt`: matches either of two regexes
         |  R*      -- `star`: matches arbitrary many repetitions of a Regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- The `Matches r s` predicate indicates that the regular expression `r` matches
the string `s` (where the string is a sequence of atoms). -/

inductive Matches {α : Type} : Regex α → List α → Prop
| empty :
  Matches Regex.empty []
| atom (a : α) :
  Matches (Regex.atom a) [a]
| concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
    (h₂ : Matches r₂ s₂) :
  Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
  Matches (Regex.alt r₁ r₂) s
| alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
  Matches (Regex.alt r₁ r₂) s
| star_base (r : Regex α) :
  Matches (Regex.star r) []
| star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
    (h₂ : Matches (Regex.star r) s') :
  Matches (Regex.star r) (s ++ s')

/- The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

2.1 (1 point). Explain why there is no rule for `nothing`. -/

/- Answer: By default, an inductive predicate is false, unless there is an
introduction rule handling a case. False is what we want for `nothing`. -/

/- 2.2 (4 points). Prove the following inversion rules. -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
  Matches (Regex.atom a) s ↔ s = [a] :=
  by
    apply Iff.intro
    { intro h
      cases h
      rfl }
    { intro h
      rw [h]
      apply Matches.atom }

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
  ¬ Matches Regex.nothing s :=
  by
    intro h
    cases h

@[simp] theorem Matches_empty {α : Type} {s : List α} :
  Matches Regex.empty s ↔ s = [] :=
  by
    apply Iff.intro
    { intro h
      cases h
      rfl }
    { intro h
      rw [h]
      apply Matches.empty }

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
  Matches (Regex.concat r₁ r₂) s
  ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | concat _ _ s₁ s₂ =>
        apply Exists.intro s₁
        apply Exists.intro s₂
        aesop }
    { intro h
      cases h with
      | intro w h =>
        cases h with
        | intro w' h =>
          cases h with
          | intro hr₁ h' =>
            cases h' with
            | intro hr₂ hs =>
              rw [hs]
              apply Matches.concat <;>
                assumption }

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
  Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) :=
  by
    apply Iff.intro
    { intro h
      cases h <;>
        aesop }
    { intro h
      cases h
      { apply Matches.alt_left
        assumption }
      { apply Matches.alt_right
        assumption } }

/- 2.3 (1 bonus point). Prove the following inversion rule. -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
  Matches (Regex.star r) s ↔
  (s = [] ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂)) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | star_base =>
        aesop
      | star_step _ s s' =>
        apply Or.intro_right
        apply Exists.intro s
        apply Exists.intro s'
        simp [*] }
    { intro h
      cases h with
      | inl h =>
        rw [h]
        apply Matches.star_base
      | inr h =>
        cases h with
        | intro w₁ h =>
          cases h with
          | intro w₂ h =>
            cases h with
            | intro hw₁ h' =>
              cases h' with
              | intro hw₂ hs =>
                rw [hs]
                apply Matches.star_step <;>
                  assumption }

end LoVe
