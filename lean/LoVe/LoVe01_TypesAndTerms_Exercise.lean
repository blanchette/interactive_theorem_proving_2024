/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_DemoMaster


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
--sol   sorry
  fun g b a ↦ g a b
--los

def projFst : α → α → α :=
--sol   sorry
  fun x y ↦ x
--los

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
--sol   sorry
  fun x y ↦ y
--los

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
--sol   sorry
  fun g a f b ↦ g a b
--los


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. You might find the characters `–` (to draw horizontal
bars) and `⊢` useful. -/

--sol -- write your solution in a comment here or on paper
/- Let `D` := `g : α → β → γ, b : β, a : α`. We have

    –––––––––––––––––– Var    –––––––––– Var
    D ⊢ g : α → β → γ         D ⊢ a : α
    –––––––––––––––––––––––––––––––––––– App    –––––––––– Var
    D ⊢ g a : β → γ                             D ⊢ b : β
    –––––––––––––––––––––––––––––––––––––––––––––––––––––– App
    D ⊢ g a b : γ
    ––––––––––––––––––––––––––––––––––––––––––––––––--- Fun
    g : α → β → γ, b : β ⊢ (fun a : α ↦ g a b) : α → γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––------- Fun
    g : α → β → γ ⊢ (fun (b : β) (a : α) ↦ g a b) : β → α → γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––––---------------------- Fun
    ⊢ (fun (g : α → β → γ) (b : β) (a : α) ↦ g a b) : (α → β → γ) → β → α → γ -/
--los

end LoVe
