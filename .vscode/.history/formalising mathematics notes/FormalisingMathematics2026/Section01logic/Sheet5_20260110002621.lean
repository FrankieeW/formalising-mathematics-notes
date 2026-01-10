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
  rwa [h1] -- or rw[h1, h2]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · rintro ⟨left, right⟩
    constructor <;> assumption
  · intro h
    constructor
    · exact h.right
    · exact h.left



example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨⟨p, q⟩, r⟩
    constructor
    · exact p
    · constructor
      · exact q
      · exact r
  · rintro ⟨p, ⟨q, r⟩⟩
    constructor
    · constructor
      · exact p
      · exact q
    · exact r

-- Alternately:
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨⟨p, q⟩, r⟩
    exact ⟨p, q, r⟩
  · rintro ⟨p, q, r⟩
    exact ⟨⟨p, q⟩, r⟩

example : P ↔ P ∧ True := by
  constructor
  · intro hP
    exact ⟨hP, trivial⟩
  · intro h
    exact h.left

example : False ↔ P ∧ False := by
  constructor
  · intro hF
    exfalso
    exact hF
  · rintro ⟨_, hF⟩
    exact hF

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor
  · rintro ⟨hP, hR⟩
    constructor
    · rw [hPQ] at hP
      exact hP
    · rw [hRS] at hR
      exact hR
  · rintro ⟨hQ, hS⟩
    constructor
    · rw [←hPQ] at hQ
      exact hQ
    · rw [←hRS] at hS
      exact hS

-- Alternately:
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor
  · rintro ⟨hP, hR⟩
    exact ⟨hPQ.mp hP, hRS.mp hR⟩
  · rintro ⟨hQ, hS⟩
    exact ⟨hPQ.mpr hQ, hRS.mpr hS⟩


example : ¬(P ↔ ¬P) := by
  change (P ↔ P → False) → False
  intro h
  rw [h]
  
