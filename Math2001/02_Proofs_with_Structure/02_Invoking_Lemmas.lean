/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  ## 2.2. Invoking lemmas
-/

-- 2.2.1. Example
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt  -- changes the goal
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

-- 2.2.2. Example
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    0 < 1 := by numbers
    _ ≤ y ^ 2 + 1 := by extra

-- 2.2.3. Example
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm -- split into two goals!
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


/-! ### 2.2.4. Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h1 : m = 4 := by addarith [hm]
  calc
    6 < 3 * 4 := by numbers
    _ = 3 * m := by rw [h1]

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc  -- ⊢ s ≤ -2
    s = 3 * s / 3 := by ring
    _ ≤ -6 / 3 := by rel [h1]
    _ = -2 := by ring
  calc  -- ⊢ s ≥ -2
    s = 2 * s / 2 := by ring
    _ ≥ -4 / 2 := by rel [h2]
    _ = -2 := by ring
