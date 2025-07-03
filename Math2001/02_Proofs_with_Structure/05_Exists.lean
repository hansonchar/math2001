/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  ## 2.5. Existence proofs
-/

/-!
  ### 2.5.1. Example
-/
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

/-!
  ### 2.5.2. Example
-/
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0 -- Note this hypothesis is always true, i.e., needs no justification
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt] -- hx: x ≤ 0
    have hx' : 0 ≤ -x := by addarith [hx]
    -- We can cancel `-x` from `0 < -x * t` even if we only have `0 ≤ -x`.
    -- `cancel` appears to be smart enought to figure that `x` could not be zero in this case.
    cancel -x at hxt' -- interesting use of `cancel`, directly modifying `hxt'`!
    apply ne_of_gt  -- ⊢ 0 < t
    apply hxt'
  . have hxt' : 0 < -x * t := by addarith [hxt] -- hx: x > 0
    have ht : 0 < x * (-t) := by
      calc
        0 < -x * t := hxt'
        _ = x * -t := by ring
    cancel x at ht  -- we can cancel `x` from `0 < x * -t` when we can establish that `x > 0`.
    have ht' : t < 0 := by addarith [ht]
    apply ne_of_lt  -- ⊢ t < 0
    exact ht'

-- It appears that for `cancel` to work we have to move all the terms to the positive side.
example {t x : ℝ} (h1 : 0 < x * t) (h2 : x > 0) : t > 0 := by
  cancel x at h1

/-!
  ### 2.5.3. Example
-/
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

/-!
  ### 2.5.4. Example
-/
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

/-!
  ### 2.5.5. Example
-/
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5  -- cute
  numbers

/-!
  ### 2.5.6. Example
-/
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1), a
  ring  -- cute

/-!
  ### 2.5.7. Example
-/
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2 -- ⊢ p < (p + q) / 2 ∧ (p + q) / 2 < q
  constructor
  calc  -- ⊢ p < (p + q) / 2
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  calc  -- ⊢ (p + q) / 2 < q
    (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring

/-!
  ### 2.5.8. Example

  The Taxicab number!
-/
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor -- ⊢ 1 ^ 3 + 12 ^ 3 = 1729
  numbers
  constructor -- ⊢ 9 ^ 3 + 10 ^ 3 = 1729
  numbers
  constructor -- ⊢ 1 ≠ 9
  numbers  -- ⊢ 1 ≠ 10
  numbers

/-! ### 2.5.9. Exercises -/

-- Exercise 2.5.9.1.
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry

-- Exercise 2.5.9.2.
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

-- Exercise 2.5.9.3.
example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry

-- Exercise 2.5.9.4.
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry

-- Exercise 2.5.9.5.
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

-- Exercise 2.5.9.6.
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

-- Exercise 2.5.9.7.
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

-- Exercise 2.5.9.8.
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

-- Exercise 2.5.9.9.
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
