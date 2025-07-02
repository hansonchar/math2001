/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  ## 2.4. “And”

  ### 2.4.1. Example

  Remark: uses obtain to split a ∧ in a hypothesis into two hypotheses.
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

/-!
  ### 2.4.3. Example

  `constructor` splits a goal with `∧` into two goals.
-/
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc          -- ⊢ a = 9
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2] -- ⊢ b = 1

/-!
  Alternatively, there might be an intermediate fact which you wish to note and then use in both parts of the proof. For example, you might want to first solve for $b$, and then use that to shorten the work of solving for $a$.
-/
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb

/-!
  ### 2.4.4. Example
-/
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc  -- ⊢ a ^ 2 ≤ 0
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    -- ⊢ 0 ≤ a ^ 2
    extra
  constructor
  -- ⊢ a = 0
  cancel 2 at h2
  -- ⊢ b = 0
  have h3: b ^ 2 = 0
  calc
    b ^ 2 = 0 + b ^ 2 := by ring
    _ = a ^ 2 + b ^ 2 := by rw [h2]
    _ = 0 := by rw [h1]
  cancel 2 at h3

/-! ### 2.4.5. Exercises -/

-- Exercise 2.4.5.1
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + (a + b) := by rel [h1]
    _ ≤ 1 + 3 := by rel [h2]
    _ = 4 := by numbers

-- Exercise 2.4.5.2
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = r + s + (r - s) := by ring
    _ ≤ 1 + (r - s) := by rel [h1]
    _ ≤ 1 + 5 := by rel [h2]
    _ = 6 := by numbers

-- Exercise 2.4.5.3
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m = m + 5 - 5 := by ring
    _ ≤ n - 5 := by rel [h2]
    _ ≤ 8 - 5 := by rel [h1]
    _ = 3 := by numbers

-- Exercise 2.4.5.4
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : p ≥ 7 := by addarith [hp]
  constructor
  calc
    p ^ 2 = p * p := by ring
    _ ≥ 7 * 7 := by rel [h1]
    _ = 49 := by numbers
  addarith [h1]

-- Exercise 2.4.5.5
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h1 : a ≥ 6 := by addarith [h]
  constructor
  exact h1    -- apply h1 also works; I learned the use of exact from nng4.
  calc
    3 * a ≥ 3 * 6 := by rel [h1]
    _ ≥ 10 := by numbers

-- Exercise 2.4.5.6
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : 2 * x + 2 * y = 10 := by  -- h3 seemed like a good idea.
    calc
      2 * x + 2 * y = 2 * (x + y) := by ring
      _ = 2 * 5 := by rw [h1]
      _ = 10 := by numbers
  have h4 : x = 3 := by -- and so did h4.
    calc
      x = 2 * x + 2 * y - (x + 2 * y) := by ring
      _ = 10 - (x + 2 * y) := by rw [h3]
      _ = 10 - 7 := by rw [h2]
      _ = 3 := by numbers
  constructor
  exact h4
  calc
    y = x + y - x := by ring
    _ = 5 - x := by rw [h1]
    _ = 5 - 3 := by rw [h4]
    _ = 2 := by numbers

-- Exercise 2.4.5.7
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  sorry
