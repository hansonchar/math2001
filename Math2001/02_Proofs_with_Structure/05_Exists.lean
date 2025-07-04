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
  use 1.3
  numbers

-- Exercise 2.5.9.2.
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2, 9
  numbers

-- Exercise 2.5.9.3.
example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers -- ⊢ -0.5 < 0
  numbers -- ⊢ (-0.5)^2 < 1

-- Exercise 2.5.9.4.
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

-- Exercise 2.5.9.5.
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  obtain hx | hx := le_or_gt x 0
  -- First case. hx: x ≤ 0
  use x - 1
  have hx' : -x ≥ 0 := by addarith [hx]
  have hxx : -x ≥ x := by
    calc
      -x = -x := by rfl
      _ ≥ 0 := hx'
      _ ≥ x := hx

  -- We introduce the next hypothesis so that, later on, we can turn `-x` into `p`, a form without
  -- the minus sign. This led to breaking through the barrier of using `extra`, which in addition
  -- requires the existence of a hypothesis that `p ≥ 0`.
  have P : ∃ p, p = -x
  use -x
  rfl

  obtain ⟨p, hpx⟩ := P -- hpx: p = -x
  have hxp : -x = p := by addarith [hpx]
  have hpz : p ≥ 0 := by
    calc
      p = -x := hpx
      _ ≥ 0 := hx'
  calc
    (x - 1) ^ 2 = x ^ 2 + (-x) + (-x) + 1 := by ring -- it has to be `+ (-x)` for the next step to
    _ = x^2 + p + p + 1 := by rw [hxp]  -- work.
    _ ≥ p + 1 := by extra -- implicitly makes use of `hpz`
    _ > p := by extra
    _ = -x := by rw [hpx]
    _ ≥ x := by rel [hxx]

  -- Second case. hx: x > 0
  use x + 1
  calc
    (x + 1)^2 = x ^ 2 + x + x + 1 := by ring
    _ > x ^ 2 + x + x := by extra
    _ ≥ x := by extra

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Example.201.2E4.2E6.20of.20The.20Mechanics.20of.20Proof/near/527103874
-- Experiments on `extra`.
example (p: ℝ) (hp: p ≥ 0) : 2 * p ≥ p := by
calc
  2 * p = p + p := by ring
  _ ≥ p := by extra

-- `rel` can be used instead.
example (p: ℝ) (hp: p ≥ 0) : 2 * p ≥ p := by
calc
  2 * p = p + p := by ring
  _ ≥ p + 0 := by rel [hp]
  _ = p := by ring

-- This doesn't work. It seems `extra` works only specifically for adding non-negative quantities.
-- example (q: ℝ) (hq: q ≤ 0) : 2 * q ≤ q := by
-- calc
--   2 * q = q + q := by ring
--   _ ≤ q + 0 := by extra

-- We need to use `rel` instead:
example (q: ℝ) (hq: q ≤ 0) : 2 * q ≤ q := by
calc
  2 * q = q + q := by ring
  _ ≤ q + 0 := by rel [hq]
  _ = q := by ring

-- `extra` comes in handy when there is square involved, e.g.
example (n: ℝ) : 0 ≤ n^2 := by extra

example (q: ℝ) (hq: q ≤ 0) : 2 * q ≤ q := by
  have hq' : q ≥ 2 * q := by
    calc
      q = q + 0 := by ring
      _ ≥ q + q := by rel [hq]
      _ = 2 * q := by ring
  addarith [hq']

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
