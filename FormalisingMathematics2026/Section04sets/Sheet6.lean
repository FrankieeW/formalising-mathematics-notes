/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

REMARK: 函数作用在集合上的像与逆像


-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by --
  intro x h
  -- rw [Set.mem_preimage]
  use x


example : f '' (f ⁻¹' T) ⊆ T := by
  intro y h
  -- rw [Set.mem_image] at h
  obtain ⟨x, h1, h2⟩ := h
  -- rw [Set.mem_preimage] at h1
  have h1: f x ∈ T := h1
  exact h2 ▸ h1

-- `exact?` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h1 x h2
    apply h1
    use x
  · intro h1 y h2
    obtain ⟨x, h3, h4⟩ := h2
    have h5 : x ∈ f ⁻¹' T := h1 h3
    exact h4 ▸ h5

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext x
  rfl
  -- constructor <;>
  --   · intro h
  --     exact h

-- pushforward is a little trickier. You might have to `ext x`, `constructor`.
example : id '' S = S := by
  ext x
  constructor
  ·
    intro h
    obtain ⟨y, h1, h2⟩ := h
    -- have h2 : y = x := h2
    exact h2 ▸ h1
  ·
    intro h
    -- rw [Set.mem_image] -- for understanding no need to do this
    use x
    constructor
    · exact h
    · rfl

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : (g ∘ f) ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  rfl

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext z
  constructor
  ·
    rintro ⟨y, h1, h2⟩
    -- apply Exists.intro (f y)
    use f y
    have h3 : f y ∈ f '' S := Exists.intro y ⟨h1, rfl⟩
    constructor
    · exact h3
    · exact h2
  ·
    rintro ⟨y, ⟨x, h3, h4⟩, h2⟩
    -- apply Exists.intro x
    use x
    constructor
    · exact h3
    ·
      -- have h5 : g (f x) = z := h2 ▸ h4 ▸ rfl
      -- explain: h2 :  g y = z and h4 : f x = y
      -- rfl: g (f x) = g (f x)
      -- h4 ▸ rfl: g (f x) = g y
      -- h2 ▸ (h4 ▸ rfl): g (f x) = z
      -- exact h5
      exact h2 ▸ h4 ▸ rfl
