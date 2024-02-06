/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe Homework 7 (10 points + 1 bonus point): Monads

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): `map` for Monads

We will define a `map` function for monads and derive its so-called functorial
properties from the three laws.

1.1 (2 points). Define `map` on `m`. This function should not be confused
with `mmap` from the lecture's demo.

Hint: The challenge is to find a way to create a value of type `m β`. Follow the
types. Inventory all the arguments and operations available (e.g., `pure`,
`>>=`) with their types and see if you can plug them together like Lego
bricks. -/

def map {m : Type → Type} [LawfulMonad m] {α β : Type} (f : α → β) (ma : m α) :
  m β := :=
  sorry

/- 1.2 (1 point). Prove the identity law for `map`.

Hint: You will need `LawfulMonad.bind_pure`. -/

theorem map_id {m : Type → Type} [LawfulMonad m] {α : Type}
    (ma : m α) :
  map id ma = ma :=
  sorry

/- 1.3 (2 points). Prove the composition law for `map`. -/

theorem map_map {m : Type → Type} [LawfulMonad m] {α β γ : Type}
    (f : α → β) (g : β → γ) (ma : m α) :
  map g (map f ma) = map (fun x ↦ g (f x)) ma :=
  sorry


/- ## Question 2 (5 points + 1 bonus point): Monadic Structure on Lists

`List` can be seen as a monad, similar to `Option` but with several possible
outcomes. It is also similar to `Set`, but the results are ordered and finite.
The code below sets `List` up as a monad. -/

namespace List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      f => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α :=
  [a]

/- 2.1 (1 point). Prove the following property of `bind` under the append
operation. -/

theorem bind_append {α β : Type} (f : α → List β) :
  ∀as as' : List α, bind (as ++ as') f = bind as f ++ bind as' f :=
  sorry

/- 2.2 (3 points). Prove the three laws for `List`. -/

theorem pure_bind {α β : Type} (a : α) (f : α → List β) :
  bind (pure a) f = f a :=
  sorry

theorem bind_pure {α : Type} :
  ∀as : List α, bind as pure = as :=
  sorry

theorem bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ) :
  ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) :=
  sorry

/- 2.3 (1 point). Prove the following list-specific law. -/

theorem bind_pure_comp_eq_map {α β : Type} {f : α → β} :
  ∀as : List α, bind as (fun a ↦ pure (f a)) = List.map f as :=
  sorry

/- 2.4 (1 bonus point). Register `List` as a lawful monad: -/

instance LawfulMonad : LawfulMonad List :=
  sorry

end List

end LoVe
