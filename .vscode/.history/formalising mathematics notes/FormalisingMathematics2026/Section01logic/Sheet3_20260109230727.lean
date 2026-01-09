/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change` : changes the goal or a hypothesis to a definitionally equal one (can omit?)
* `by_contra` : proves `P` by assuming `¬ P → False`
* `by_cases` : proves `P` by considering the cases

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  -- change True → False at h
  apply h
  trivial


example : False → ¬True := by
  -- change False → (True → False)
  intro hF hT
  exact hF

example : ¬False → True := by
  -- intro h
  trivial

example : True → ¬False := by
  -- change True → (False → False)
  intro hT hF
  exact hF

example : False → ¬P := by
  intro hF hP
  exact hF

example : P → ¬P → False := by
  intro hP hNP
  -- change P → False at hNP
  apply hNP
  exact hP

example : P → ¬P → False := by
  intro hP hNP
  exact hNP hP


example : P → ¬¬P := by
  intro hP hNP
  exact hNP hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hNQ hP
  apply hNQ
  apply hPQ
  exact hP

example : ¬¬False → False := by
  intro hNNF
  apply hNNF
  intro hF
  exact hF

example : ¬¬P → P := by
  sorry

example : (¬Q → ¬P) → P → Q := by
  sorry
