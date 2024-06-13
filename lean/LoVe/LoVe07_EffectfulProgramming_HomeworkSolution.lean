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
  m β :=
  ma >>= (fun a ↦ pure (f a))

/- 1.2 (1 point). Prove the identity law for `map`.

Hint: You will need `LawfulMonad.bind_pure`. -/

theorem map_id {m : Type → Type} [LawfulMonad m] {α : Type}
    (ma : m α) :
  map id ma = ma :=
  calc
    map id ma = ma >>= fun a ↦ pure (id a) :=
      by rfl
    _ = ma >>= fun a ↦ pure a :=
      by rfl
    _ = ma :=
      LawfulMonad.bind_pure ma

/- 1.3 (2 points). Prove the composition law for `map`. -/

theorem map_map {m : Type → Type} [LawfulMonad m] {α β γ : Type}
    (f : α → β) (g : β → γ) (ma : m α) :
  map g (map f ma) = map (fun x ↦ g (f x)) ma :=
  calc
    map g (map f ma)
    = (ma >>= (fun a ↦ pure (f a)) >>= (fun a ↦ pure (g a))) :=
      by rfl
    _ = ma >>= fun a ↦ (pure (f a) >>= (fun a ↦ pure (g a))) :=
      LawfulMonad.bind_assoc _ _ _
    _ = ma >>= fun a ↦ pure (g (f a)) :=
      by simp [LawfulMonad.pure_bind]
    _ = ma >>= fun a ↦ pure ((g ∘ f) a) :=
      by rfl
    _ = map (fun x ↦ g (f x)) ma :=
      by rfl


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
  ∀as as' : List α, bind (as ++ as') f = bind as f ++ bind as' f
  | [],      as' => by rfl
  | a :: as, as' => by simp [bind, bind_append _ as as']

/- 2.2 (3 points). Prove the three laws for `List`. -/

theorem pure_bind {α β : Type} (a : α) (f : α → List β) :
  bind (pure a) f = f a :=
  by simp [pure, bind]

theorem bind_pure {α : Type} :
  ∀as : List α, bind as pure = as
  | []      => by rfl
  | a :: as =>
    by
      rw [bind]
      rw [pure]
      simp
      apply bind_pure

theorem bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ) :
  ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g)
  | []      => by rfl
  | a :: as => by simp [bind, bind_append, bind_assoc _ _ as]

/- 2.3 (1 point). Prove the following list-specific law. -/

theorem bind_pure_comp_eq_map {α β : Type} {f : α → β} :
  ∀as : List α, bind as (fun a ↦ pure (f a)) = List.map f as
  | []      => by rfl
  | a :: as =>
    by
      rw [bind]
      rw [pure]
      simp
      apply bind_pure_comp_eq_map

/- 2.4 (1 bonus point). Register `List` as a lawful monad: -/

instance LawfulMonad : LawfulMonad List :=
  { pure       := pure
    bind       := bind
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, pure_bind]
    bind_pure  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, bind_pure]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Pure.pure, Bind.bind, bind_assoc] }

end List

end LoVe
