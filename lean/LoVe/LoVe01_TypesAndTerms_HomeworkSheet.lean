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
  sorry

def S : (α → β → γ) → (α → β) → α → γ :=
  sorry

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  sorry

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  sorry

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  sorry

/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above, using ASCII or
Unicode art. You might find the characters `–` (to draw horizontal bars) and `⊢`
useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

end LoVe
