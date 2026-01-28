/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro h1 h2
  exact h1 h2

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  exact h2 h1

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro h1 h2 h3
  exact h2 (h1 h3)

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro h
  exact h

example : x ∈ Aᶜ ↔ x ∉ A := by
  rw [Set.mem_compl_iff]

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro h1 h2
    obtain ⟨y, h3⟩ := h2
    exact h3 (h1 y)
  ·
    intro h1 x
    by_contra h2
    have h3 : ∃ x, x ∈ Aᶜ := ⟨x, h2⟩
    exact h1 h3

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · intro h1 h2
    obtain ⟨y, h3⟩ := h1
    exact h2 y h3
  ·
    intro h1
    by_contra h2
    push_neg at h1 h2
    obtain ⟨y, h3⟩ := h1
    exact h3 (h2 y)
