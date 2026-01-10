/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl` to prove things that are true by definition
* `rw` to rewrite using an `iff` hypothesis

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  have h : (P ↔ Q) → (Q ↔ P) := by
    intro h1
    rw [h1]
  have h' : (Q ↔ P) → (P ↔ Q) := by
    intro h2
    rw [h2]
  -- rw [iff_iff_implies_and_implies]
  constructor <;> assumption

--  Alternately:
example : (P ↔ Q) ↔ (Q ↔ P) := by
  -- rw [iff_iff_implies_and_implies]
  constructor
  · intro h1
    rw [h1]
  · intro h2
    rw [h2]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw [h1, h2]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  sorry

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry

example : P ↔ P ∧ True := by
  sorry

example : False ↔ P ∧ False := by
  sorry

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry

example : ¬(P ↔ ¬P) := by
  sorry
