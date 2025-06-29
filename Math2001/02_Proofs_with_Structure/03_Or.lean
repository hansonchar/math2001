/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  ## 2.3. “Or” and proof by cases

  ### 2.3.1. Example
-/

example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

/-!
  ### 2.3.2. Example

  Let be any natural number. Show that $n^2 ≠ 2$.

  In general, a natual number $n$ is either ≤ to one natural number (such as 1),
  or it’s ≥ the next one (such as 2).
-/
example {n : ℕ} : n ^ 2 ≠ 2 := by
  -- Introduce the hypothesis: n ≤ 1 ∨ 2 ≤ n.
  have hn := le_or_succ_le n 1  -- We have not previously invoked lemmas in this way.
  obtain hn | hn := hn          -- `obtain` is also new. It splits a hypothesis into cases.
  . apply ne_of_lt                -- Tackle the first case, namely, hn: n ≤ 1.
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  . apply ne_of_gt                -- Tackle the second case, namely, hn : 2 ≤ n.
    calc
      2 ≤ n := by rel [hn]  -- we want $2n$ to appear on the right, so we can invoke `rel [hn]`
      _ < n + n := by extra
      _ = 2 * n := by ring
      _ ≤ n * n := by rel [hn]
      _ = n ^ 2 := by ring

/-!
  ### 2.3.3. Example
-/
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers

/-!
  ### 2.3.4. Example

  This example involes creating a hypothesis with an "or", so it can be split into cases.
  Also split the goal into cases and prove each case.
-/
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  -- Note the interesting construction of `h1` without explicitly saying what it is upfront!
  have h1 :=
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0 := by rw [hx] -- h1: (x - 1) * (x - 2) = 0
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1 -- h2: (x - 1 = 0) ∨ (x - 2 = 0)
  obtain h3 | h3 := h2  -- split h2 into two cases, h3: x - 1 = 0
                        --                          h3: x - 2 = 0
  left  -- select the left goal to prove: x = 1
  calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h3]
    _ = 1 := by numbers
  right
  calc  -- select the right goal to prove: x = 2
    x = x - 2 + 2 := by ring
    _ = 0 + 2 := by rw [h3]
    _ = 2 := by numbers

/-!
  ### 2.3.5. Example

  In Example 2.3.2 we showed that no natural number squares to 2.
  It is also true that no integer squares to 2, but since order laws are more complicated when
  negative numbers are involved, the proof is more complicated, requiring cases within cases.

  When a proof becomes this complicated, you may find it helpful to mark the start of each
  new sub-proof with the symbol `·`, as follows.
-/
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0         --  hn0: n ≤ 0 ∨ 1 ≤ n
  obtain hn0 | hn0 := hn0
                                        --  hn0: n ≤ 0
  · have : 0 ≤ -n := by addarith [hn0]  -- this: 0 ≤ -n
    have hn := le_or_succ_le (-n) 1     --   hn: -n ≤ 1 ∨ 2 ≤ -n
    obtain hn | hn := hn
                                        -- hn: -n ≤ 1
    · apply ne_of_lt                    -- ⊢ n ^ 2 < 2
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
                                        -- hn: 2 ≤ -n
    · apply ne_of_gt                    -- ⊢ 2 < n ^ 2
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        -- This also seems to work. So why (2:ℤ) ?
        -- 2 < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
                                      -- hn0: 1 ≤ n
  · have hn := le_or_succ_le n 1      --  hn: n ≤ 1 ∨ 2 ≤ n
    obtain hn | hn := hn
                                      --  hn: n ≤ 1
    · apply ne_of_lt                  -- ⊢ n ^ 2 < 2
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
                                      --  hn: 2 ≤ n
    · apply ne_of_gt                  -- 2 < n ^ 2
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! ### 2.3.6. Exercises -/

-- Exercise 2.3.6.1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h1 := h -- Split h into cases. Then prove each case.
  calc
    x ^ 2 + 1 = 4 ^ 2 + 1 := by rw [h1]
    _ = 17 := by numbers
  calc
    x ^ 2 + 1 = (-4) ^ 2 + 1 := by rw [h1]
    _ = 17 := by numbers

-- Exercise 2.3.6.2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  calc
    x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [h]
    _ = 0 := by numbers
  calc
    x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [h]
    _ = 0 := by numbers

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  sorry

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

example {t : ℤ} : 5 * t ≠ 18 := by
  sorry

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
