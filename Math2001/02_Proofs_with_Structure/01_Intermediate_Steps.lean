/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.1.1. Example
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

-- 2.1.2. Example
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]

/-!
  This also works, and arguably a more consistent style (having the additional `by`):
-/
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 := by
    calc
      m + 3 ≤ 2 * n - 1 := by rel [h1]
      _ ≤ 2 * 5 - 1 := by rel [h2]
      _ = 9 := by numbers
  addarith [h3]

-- 2.1.3. Example
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith [h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

-- 2.1.4. Example
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]

-- 2.1.5. Example
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3

-- 2.1.6. Example
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h3 : x ≤ -1 := by addarith [hx]        -- addaridth is so handy!
  have h4 : y ≥ 3 - 2 * x := by addarith [hy]
  calc
    y ≥ 3 - 2 * x := by rel [h4]
    _ ≥ 3 - 2 * -1 := by rel [h3]
    _ > 3 := by numbers

-- 2.1.7. Example
-- Initial attempt before reading the details.
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : b + a ≥ 0 := by addarith [h1]
  have h4 : b - a ≥ 0 := by addarith [h2]
  have h5 : b^2 - a^2 ≥ 0 := by
    calc
      b ^ 2 - a ^ 2 = (b + a) * (b - a) := by ring
      _ ≥ 0 * 0 := by rel [h3, h4]
      _ = 0 := by numbers
  calc
    a^2 ≤ b^2 := by addarith [h5]

/-!
  Retrospect: The key was to make use of the fact that $(b+a)(b-a)=b^2-a^2$.
-/

-- Second attempt after reading the [details](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#prove-sq-le-sq).
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : b + a ≥ 0 := by addarith [h1]
  have h4 : b - a ≥ 0 := by addarith [h2]
  calc
    a ^ 2 ≤ a ^ 2 + (b + a) * (b - a) := by extra -- courtesy of the power of Lean, we don't
    _ = b ^ 2 := by ring -- need to even explicilty refer to h3 and h4 (even though they have to be present)!

-- [2.1.8. Example](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#cube-inequality)
-- Assuming the given information is correct, all we need to do is to figure out the
-- intermediare step, i.e, h1, and let lean do the rest!
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : 0 ≤ b - a := by addarith [h]
  calc
    a^3 ≤ a ^ 3 + ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 := by extra
    _ = b^3 := by ring

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  sorry

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  sorry
