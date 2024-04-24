/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 1 (10 points): Types and Terms

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Terms

We start by declaring four new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1 (4 points). Complete the following definitions, by providing terms with
the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

def B : (α → β) → (γ → α) → γ → β :=
--sol   sorry
  fun g f c ↦ g (f c)
--los

def S : (α → β → γ) → (α → β) → α → γ :=
--sol   sorry
  fun g f a ↦ g a (f a)
--los

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
--sol   sorry
  fun h c b ↦ h (fun x ↦ b) c
--los

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
--sol   sorry
  fun f g a b ↦ g a
--los

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
--sol   sorry
  fun f ↦ f (fun g ↦ g (fun a ↦ f (fun h ↦ a)))
--los

/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above, using ASCII or
Unicode art. You might find the characters `–` (to draw horizontal bars) and `⊢`
useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

--sol -- write your solution here
/- Let C := g : α → β, f : γ → α, c : γ. We have

    –––––––––––––– Var  –––––––––––––– Var  –––––––––– Var
    C ⊢ g : α → β       C ⊢ f : γ → α       C ⊢ c : γ
    –––––––––––––– Var  –––––––––––––––––––––––––––––– App
    C ⊢ g : α → β       C ⊢ f c : α
    –––––––––––––––––––––––––––––––– App
    C ⊢ g (f c) : β
    –––––––––––––––––––––––––––––––––––––––––––––––– Fun
    g : α → β, f : γ → α ⊢ (fun c ↦ g (f c)) : γ → β
    ––––––––––––––––––––––––––––––––––––––––––––––––– Fun
    g : α → β ⊢ (fun f c ↦ g (f c)) : (γ → α) → γ → β
    ––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
    ⊢ (fun g f c ↦ g (f c)) : (α → β) → (γ → α) → γ → β -/
--los

end LoVe
