/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h =>
  intro hPtoR hQtoR
  exact hPtoR h
  | inr h =>
  intro hPtoR hQtoR
  exact hQtoR h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · intro hPtoR hQtoR
    exact hPtoR h
  · intro hPtoR hQtoR
    exact hQtoR h

example : P ∨ Q → (P → R) → (Q → R) → R := by
--  mark
  rintro (h | h)
  · intro hPtoR _
    exact hPtoR h
  · intro _ hQtoR
    exact hQtoR h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (h|h)
  · right
    exact h
  · left
    exact h

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro (h|h)
    -- · cases h with
    -- | inl h =>
    --     left
    --     exact h
    -- | inr h =>
    --     right
    --     left
    --     exact h
    · rcases h with hP | hQ
      · left
        exact hP
      · right
        left
        exact hQ
    · right
      right
      exact h
  · rintro (h|h)
    · left
      left
      exact h
    · cases h with
    | inl h =>
      left
      right
      exact h
    | inr h => right; exact h

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPtoR hQtoS
  rintro (hP|hQ)
  · left
    exact hPtoR hP
  . right
    exact hQtoS hQ


example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPtoQ
  rintro (hP|hR)
  · left
    exact hPtoQ hP
  · right
    exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  constructor
  · rintro (hP|hQ)
    · left
      exact hPR.mp hP
    · right
      -- exact hQS.mp hQ
      rw [hQS] at hQ
      exact hQ
  · rintro (h|h)
    · left
      rw [← hPR] at h
      exact h
    · right
      rw [← hQS] at h
      exact h


-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  -- · intro h
  --   constructor
  --   · intro hP
  --     apply h
  --     left
  --     exact hP
  --   · intro hQ
  --     apply h
  --     right
  --     exact hQ
  · rintro h
    constructor
    · intro hP
      exact h (Or.inl hP)
    · intro hQ
      exact h (Or.inr hQ)
  · rintro ⟨hNotP, hNotQ⟩ hPoQ
    rcases hPoQ with hP|hQ
    · exact hNotP hP
    · apply hNotQ
      exact hQ



example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro hNotPandQ
    by_contra h
    apply hNotPandQ
    constructor
    · by_contra hP
      apply h
      left
      exact hP
    · by_contra hQ
      apply h
      right
      exact hQ
  · rintro (hNotP|hNotQ)
    · intro hPandQ
      apply hNotP
      exact hPandQ.left
    · intro hPandQ
      apply hNotQ
      exact hPandQ.right
