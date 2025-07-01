/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  ## 2.4. “And”

  ### 2.4.1. Example

  Remark: uses obtain to split a conjunction into two hypothesis.
-/

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

/-!
  ### 2.4.2. Example

  Interesting parts:
  1. introduce a new hypothesis
  1. prove via the application (via `apply`) of `abs_le_of_sq_le_sq'`
  1. use of `.` in proving a newly introduced hypothesis
  1. the use of `numbers` and nothing else to prove a goal.
-/
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 -- conjure up `hp'` but we need to prove it.
  · apply abs_le_of_sq_le_sq' -- match `-3 ≤ p ∧ p ≤ 3` and turn into 2 subgoals.
    calc  -- First subgoal: `p ^ 2 ≤ 3 ^ 2`.
        p ^ 2 ≤ 9 := by addarith [hp]
        _ = 3 ^ 2 := by numbers
    numbers -- Second subgoal: `0 ≤ 3`.
  -- At this point, `hp'` has been established.
  obtain ⟨h1, h2⟩ := hp' -- Split `hp'` into:
  -- h1: -3 ≤ p
  -- h2: p ≤ 3
  calc
    p ≥ -3 := by rel [h1]
    _ ≥ -5 := by numbers

-- Same, but perhaps a bit easier to read.
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 -- conjure up `hp'` but we need to prove it.
  · apply abs_le_of_sq_le_sq' -- match `-3 ≤ p ∧ p ≤ 3` and turn into 2 subgoals.
    . calc  -- First subgoal: `p ^ 2 ≤ 3 ^ 2`.
        p ^ 2 ≤ 9 := by addarith [hp]
        _ = 3 ^ 2 := by numbers
    . numbers -- Second subgoal: `0 ≤ 3`.
  -- At this point, `hp'` has been established.
  obtain ⟨h1, h2⟩ := hp' -- Split `hp'` into:
  -- h1: -3 ≤ p
  -- h2: p ≤ 3
  calc
    p ≥ -3 := by rel [h1]
    _ ≥ -5 := by numbers

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  sorry

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  sorry

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  sorry

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  sorry

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  sorry

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  sorry

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  sorry

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  sorry
