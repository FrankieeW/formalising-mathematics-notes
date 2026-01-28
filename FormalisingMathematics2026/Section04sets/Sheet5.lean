/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  rw [mem_union]
  constructor
  ·
    intro h
    exact h.elim id id
  ·
    intro h
    left
    exact h


example : A ∩ A = A := by
  ext x
  constructor
  ·
    intro h
    exact h.left
  ·
    intro h
    constructor <;> exact h

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  ·
    intro h
    exact h.right
  ·
    intro h
    exfalso
    exact h

example : A ∪ univ = univ := by
  ext x
  constructor
  ·
    intro h
    trivial
  ·
    intro h
    right
    trivial

example : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext x
  constructor
  ·
    intro h
    exact h1 h
  ·
    intro h
    exact h2 h

example : A ∩ B = B ∩ A := by
  ext x
  constructor <;>
  ·
    intro h
    constructor
    ·
      exact h.right
    ·
      exact h.left



example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  ·
    -- intro h
    -- obtain ⟨h1, h2⟩ := h
    -- exact ⟨⟨h1, h2.left⟩, h2.right⟩
    rintro ⟨h1, ⟨h2, h3⟩⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  ·
    -- intro h
    -- obtain ⟨⟨ h1,h2⟩ ,h3⟩ := h
    -- exact ⟨h1, ⟨h2, h3⟩⟩
    rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, ⟨h2, h3⟩⟩


example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · intro h
    obtain h | h | h := h
    · left
      left
      exact h
    · left
      right
      exact h
    · right
      exact h
  · intro h
    obtain (h | h) | h := h
    · left
      exact h
    · right
      left
      exact h
    · right
      right
      exact h

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · constructor
      · left
        exact h
      · left
        exact h
    · constructor
      · right
        exact h1
      · right
        exact h2
  -- · rintro ⟨hA | hB, hA | hC⟩
  --   · left
  --     exact hA
  --   · left
  --     exact hA
  --   · left
  --     exact hA
  --   · right
  --     exact ⟨hB, hC⟩
  · rintro ⟨hAB, hAC⟩
    rcases hAB with hA | hB
    · left; exact hA
    rcases hAC with hA | hC
    · left; exact hA
    · right; exact ⟨hB, hC⟩




example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  · rintro ⟨hA, hBC⟩
    rcases hBC with hB | hC
    · left
      exact ⟨hA, hB⟩
    · right
      exact ⟨hA, hC⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩
