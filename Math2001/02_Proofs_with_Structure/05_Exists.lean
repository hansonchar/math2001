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
  . calc  -- ⊢ p < (p + q) / 2
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  . calc  -- ⊢ (p + q) / 2 < q
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
  . use x - 1
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
  . use x + 1
    calc
      (x + 1)^2 = x ^ 2 + x + x + 1 := by ring
      _ > x ^ 2 + x + x := by extra
      _ ≥ x := by extra

-- Alternatively, we don't need to introduce `p`:
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  obtain hx | hx := le_or_gt x 0
  -- First case. hx: x ≤ 0
  . use x - 1
    have hx' : -x ≥ 0 := by addarith [hx]
    have hxx : -x ≥ x := by
      calc
        -x = -x := by rfl
        _ ≥ 0 := hx'
        _ ≥ x := hx
    calc
      (x - 1) ^ 2 = x ^ 2 + (-x) + (-x) + 1 := by ring -- it has to be `+ (-x)` for the next step to
      _ ≥ x^2 + (-x) + 0 + 1 := by rel [hx']  -- work.
      _ = x^2 + (-x) + 1 := by ring
      _ ≥ (-x) + 1 := by extra
      _ > -x := by extra
      _ ≥ x := by rel [hxx]
  -- Second case. hx: x > 0
  . use x + 1
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

--
example {p q : ℝ} (hp : p < 0) (hq : q < 0) : p * q > 0 := by
  have hp' : -p > 0 := by addarith [hp]
  have hq' : -q > 0 := by addarith [hq]
  calc
    p * q = (-p) * (-q) := by ring
    _ > 0 := by extra -- `extra` works here because `-p` and `-q` are both positive.

-- How to cancel a term from both sides of an inequality?
example {t p : ℝ} (hp : p > 0) (ht : 0 < t * p) : 0 < t := by cancel p at ht
example {t p : ℝ} (hp : -p > 0) (ht : 0 < t * -p) : 0 < t := by cancel -p at ht

example {t p : ℝ} (hp : -p > 0) (ht : 0 > t * -p) : t < 0 := by
  have h1 : 0 < -t * -p := by addarith [ht]
  have h2 : 0 < -t := by cancel -p at h1
  addarith [h2]

example {t p : ℝ} (hp : p < 0) (ht : 0 < t * p) : t < 0 := by
  have hp' : 0 < -p := by addarith [hp]
  have h1 : 0 > t * -p := by
    calc
      0 > -(t * p) := by addarith [ht]  -- flip the inequality sign
      _ = t * -p := by ring
  have h2 : 0 < -t * -p := by addarith [h1]
  -- `cancel` works below because of two necessary conditions:
  -- 1. `-p` is positive, and
  -- 2. the rhs is > 0.
  have h3 : 0 < -t := by cancel -p at h2
  addarith [h3]

example {t p : ℝ} (hp : 1 - p > 0) (ht : 0 < t * (1 - p)) : 0 < t := by
  cancel (1 - p) at ht

-- How to prove any conclusion from a false hypothesis?
example {t : ℝ} (h : False) : t ≠ t := by
  contradiction
example {t : ℝ} (h1 : t ≠ t) : -1 = 1 := by
  contradiction

example {t : ℝ} (h1 : 0 < t) (h2 : 0 = t) : -1 = 1 := by
  have false: t ≠ t := by -- We introduce a `false` hypothesis in the necessary form,
    apply ne_of_gt  -- namely `t ≠ t`, so that we can apply `contradcition`.
    calc
      t < t + t := by addarith [h1]
      _ = t + 0 := by rw [h2]
      _ = t := by ring
  contradiction -- ⊢ t ≠ t

-- example {t : ℝ} (h1 : (t - 1) * 0 ≠ (t - 1) * 0) : -1 = 1 := by contradiction

-- Exercise 2.5.9.6.
-- First attemptm, making use of `lt_trichotomy`, and `contradiction`,
-- both have not yet been introduced.
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h         -- hx: x * t + 1 < x + t
  have hxt1 : 0 < x + t - x * t - 1 := by addarith [hxt]
  have hxt2 : 0 < (t - 1) * (1 - x) := by
    calc
      0 < x + t - x * t - 1 := hxt1
      _ = (t - 1) * (1 - x) := by ring
  have hxt3 : 0 < (1 - t) * (x - 1) := by
    calc
      0 < x + t - x * t - 1 := hxt1
      _ = (1 - t) * (x - 1) := by ring
  -- Split into three main cases.
  have H := lt_trichotomy x 0
  obtain xltz | xeqz | xgtz := H
  -- Case 1. xltz: x < 0
  . have h1 : -x > 0 := by addarith [xltz]
    have h2 : 1 - x > 0 := by
      calc
        1 - x = 1 + (-x) := by ring
        _ > 1 + 0 := by rel [h1]
        _ > 0 := by numbers
    apply ne_of_gt  -- ⊢ 1 < t
    have h6 : 0 < t - 1 := by cancel (1 - x) at hxt2
    have h7 : 1 < t := by addarith [h6]
    exact h7
  -- Case 2. xeqz: x = 0
  . have h8 : 0 = x * t := by
        calc
          0 = 0 := by rfl
          _ = 0 * t := by ring
          _ = x * t := by rw [xeqz]
    apply ne_of_gt  -- ⊢ 1 < t
    calc
      1 < x + t - x * t := by addarith [hxt]
      _ = 0 + t - x * t := by rw [xeqz]
      _ = 0 + t - 0 := by rw [h8]
      _ = t := by ring
  -- Case 3. xgtz: x > 0
  -- Further split into three sub-cases.
  . have H1 := lt_trichotomy x 1
    obtain xlt1 | xeq1 | xgt1 := H1
    -- Case 3.1. xlt1: x < 1
    . apply ne_of_gt  -- ⊢ 1 < t
      have h1 : 1 - x > 0 := by addarith [xlt1]
      have h2 : 0 < t - 1 := by cancel (1 - x) at hxt2
      addarith [h2]
    -- Case 3.2. xeq1: x = 1
    . have h3 : 1 - x = 0 := by
        calc
          1 - x = 1 - 1 := by rw [xeq1]
          _ = 0 := by numbers
      rw [h3] at hxt2
      have h4 : (t - 1) * 0 = 0 := by ring
      have false : (t - 1) * 0 ≠ (t - 1) * 0 := by
        apply ne_of_gt  -- ⊢ (t - 1) * 0 < (t - 1) * 0
        calc
          (t - 1) * 0 = (t - 1) * 0 := by rfl
          _ = (t - 1) * 0 + 0 := by ring
          _ < (t - 1) * 0 + (t - 1) * 0 := by rel [hxt2]
          _ = (t - 1) * 0 + 0 := by rw [h4]
          _ = (t - 1) * 0 := by ring
      contradiction -- ⊢ (t - 1) * 0 ≠ (t - 1) * 0
    -- Case 3.3. xgt1: x > 1
    . apply ne_of_lt  -- ⊢ t < 1
      have h1 : 0 < x - 1 := by addarith [xgt1]
      have h2 : 0 < (1 - t) := by cancel (x - 1) at hxt3
      addarith [h2]

-- Second attempt on Exercise 2.5.9.6, using only what we've learned here so far.
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨s, hst⟩ := h         -- hx: s * t + 1 < s + t
  have hst1 : 0 < s + t - s * t - 1 := by addarith [hst]
  have hst2 : 0 < (t - 1) * (1 - s) := by
    calc
      0 < s + t - s * t - 1 := hst1
      _ = (t - 1) * (1 - s) := by ring
  have hst3 : 0 < (1 - t) * (s - 1) := by
    calc
      0 < s + t - s * t - 1 := hst1
      _ = (1 - t) * (s - 1) := by ring
  -- Split into two main cases.
  have H := le_or_gt (1 - s) (t - 1)
  obtain h1 | h1 := H
  -- Case 1. h1: 1 - s ≤ t - 1
  . have S := le_or_gt (1 - s) 0
  -- Within the first case, we further split into two sub-cases.
    obtain h2 | h2 := S
    -- Case 1.1. h2: 1 - s ≤ 0
    . have h3 : s - 1 ≥ 0 := by addarith [h2] -- used implicitly in `cancel`
      have h4 : 0 < 1 - t := by cancel (s - 1) at hst3
      apply ne_of_lt  -- ⊢ t < 1
      addarith [h4]
    -- Case 1.2. h2: 1 - s > 0
    . have h3 : 0 < t - 1 := by cancel (1 - s) at hst2
      apply ne_of_gt
      addarith [h3]
  -- Case 2. h1: 1 - s > t - 1
  . have S := le_or_gt (1 - s) 0
    -- Within the second case, we further split into two sub-cases.
    obtain h2 | h2 := S
    -- Case 2.1. h2: 1 - s ≤ 0
    . have h3 : s - 1 ≥ 0 := by addarith [h2] -- used implicitly in `cancel`
      have h4 : 0 < 1 - t := by cancel (s - 1) at hst3
      apply ne_of_lt
      addarith [h4]
    -- Case 2.2. h2: 1 - s > 0
    . have h3 : 0 < t - 1 := by cancel (1 - s) at hst2
      apply ne_of_gt
      addarith [h3]

-- `cancel` works as expected.
example {p q : ℝ} (hp : 0 < p * q) (hq : q > 0) : p > 0 := by
  cancel q at hp

-- `cancel` also works in the following two cases, perhaps a little surprisingly.
-- In case `q = 0`, `hp` becomes false, so the conclusion holds vacuously.
-- More info: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.E2.9C.94.20cancel.20tactic.20on.20zero.20in.20The.20Mechanics.20of.20Proof/with/527320439
example {p q : ℝ} (hp : 0 < p * q) (hq : q ≥ 0) : p > 0 := by
  cancel q at hp
example {p q : ℝ} (hp : 0 < p * q) (hq : q = 0) : p > 0 := by
  cancel q at hp

-- Exercise 2.5.9.7.
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_gt a 2 -- H : a ≤ 5 ∨ a > 5
  obtain h1 | h2 := H
  -- h1 : a ≤ 2
  . apply ne_of_lt  -- ⊢ m < 5
    calc
      m = 2 * a := by addarith [ha]
      _ ≤ 2 * 2 := by rel [h1]
      _ < 5 := by numbers
  -- h2 : a > 2
  . apply ne_of_gt  -- ⊢ m > 5
    have h3 : a ≥ 3 := by addarith [h2]
    calc
      m = 2 * a := by addarith [ha]
      _ ≥ 2 * 3 := by rel [h3]
      _ = 6 := by numbers -- Note `m ≥ 6` satisfies `⊢ m > 5`.

/-!
  Exercise 2.5.9.8.

  The key insight is to use `n ^ 2 + 2` as a candidate for `a`. How do we come to that?

  Consider three possible cases individually:
  1. If n = 0, a ≥ 2 works.
  2. If n > 0, a ≥ n + 1 works.
  3. If n < 0, a ≥ 1 - n works.

  This suggests that n ^ 2 + 2 works in all three cases.
-/
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have h1 : n ^ 2 ≥ n := by
    have H := le_or_gt n 0
    obtain hn | hn := H
    -- hn: n ≤ 0
    . have hn' : -n ≥ 0 := by addarith [hn]
      calc
        n ^ 2 = (-n) * (-n) := by ring
        _ ≥ 0 * 0 := by rel [hn']
        _ = 0 := by numbers
        _ ≥ n := by rel [hn]
    -- hn: n > 0
    . have hn' : n ≥ 1 := by addarith [hn]
      calc
        n ^ 2 = n * n := by ring
        _ ≥ n * 1 := by rel [hn']
        _ = n := by ring
  have h2 : n ^ 4 ≥ n ^ 3 := by
    calc
      n ^ 4 = n ^ 2 * n ^ 2 := by ring
      _ ≥ n * n ^ 2 := by rel [h1]
      _ = n ^ 3 := by ring
  use n ^ 2 + 2 -- This is the key insignt. The rest follows.
  calc
    2 * (n ^ 2 + 2) ^ 3 = 2 * n ^ 6 + 12 * n ^ 4 + 24 * n ^ 2 + 7 + 9 := by ring
    _ ≥ 2 * n ^ 6 + 12 * n ^ 4 + 24 * n ^ 2 + 7 := by extra -- get rid of `+ 9`
    _ ≥ 12 * n ^ 4 + 24 * n ^ 2 + 7 := by extra -- get rid of `2 * n ^ 6`
    _ = 12 * n ^ 4 + 22 * n ^ 2 + 2 * n ^ 2 + 7 := by ring
    _ ≥ 12 * n ^ 4 + 2 * n ^ 2 + 7 := by extra  -- get rid of `22 * n ^ 2`
    _ ≥ 12 * n ^ 4 + 2 * n + 7 := by rel [h1]
    _ = 11 * n ^ 4 + n^ 4 + 2 * n + 7 := by ring
    _ ≥ n ^ 4 + 2 * n + 7 := by extra -- get rid of `11 * n ^ 4`
    _ ≥ n ^ 3 + 2 * n + 7 := by rel [h2]
    _ = n * (n ^ 2 + 2) + 7 := by ring

-- Exploring. Nice to find out!
example {n : ℝ} (h1: n ≥ 0) (h2 : n ≤ 0): n = 0 := by addarith [h1, h2]
-- example {n : ℝ} (h1: 2 * n ≥ n) (h2 : 2 * n ≤ n): n = 0 := by addarith [h1, h2]

-- Exploring.
example {n : ℝ} (h : 2 * n ≥ n) : n ≥ 0 := by
  have H := le_or_gt n 0
  obtain hn | hn := H
  -- hn: n ≤ 0
  . calc
      n = 2 * n - n := by ring
      _ ≥ n - n := by rel [h]
      _ = 0 := by ring
  -- hn: n > 0
  . addarith [hn]

-- Exploring by squeezing out more info from a + b + c.
example {a b c : ℝ} (h : 2 * (a + b + c) ≥ (a + b + c)) : (a + b + c) ≥ 0 := by
  have H := le_or_gt (a+b+c) 0
  obtain hn | hn := H
  -- hn: n ≤ 0
  . calc
      (a + b + c) = 2 * (a + b + c) - (a + b + c) := by ring
      _ ≥ (a + b + c) - (a + b + c) := by rel [h]
      _ = 0 := by ring
  -- hn: n > 0
  . addarith [hn]

/-
-- Initial struggling.
-- Exercise 2.5.9.9.
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c) / 2, (a + c) / 2, (a + b) / 2 -- This guess doesn't work.
  have h1 : a + b + c ≤ 2 * (a + b + c) := by
    calc
      a + b + c ≤ (b + c) + (a + c) + (a + b) := by rel [ha, hb, hc]
      _ = 2 * (a + b + c) := by ring
  have h2 : a + b + c ≥ 0 := by
    have H := le_or_gt (a + b + c) 0
    obtain h | h := H
    -- h: a + b + c ≤ 0
    . calc
        (a + b + c) = 2 * (a + b + c) - (a + b + c) := by ring
        _ ≥ (a + b + c) - (a + b + c) := by rel [h1]
        _ = 0 := by ring
    -- h: a + b + c > 0
    . addarith [h]
  constructor
  -- ⊢ (b + c) / 2 ≥ 0
  . have H := le_or_gt a 0
    obtain h | h := H
    -- h: a ≤ 0
    . have h' : -a ≥ 0 := by addarith [h]
      calc
        (b + c) / 2 = (a + b + c - a) / 2 := by ring
        _ ≥ (0 - a) / 2 := by rel [h2]
        _ = -a / 2 := by ring
        _ ≥ 0 / 2 := by rel [h']
        _ = 0 := by numbers
    -- ⊢ a > 0
    . calc
        (b + c) / 2 ≥ a / 2 := by addarith [ha]
        _ ≥ 0 / 2 := by rel [h]
        _ = 0 := by numbers
  constructor
  -- ⊢ a + c ≥ 0
  . have H := le_or_gt b 0
    obtain h | h := H
    -- h: b ≤ 0
    . have h' : -b ≥ 0 := by addarith [h]
      calc
        (a + c) / 2 = (a + b + c - b) / 2 := by ring
        _ ≥ (0 - b) / 2 := by rel [h2]
        _ = -b / 2 := by ring
        _ ≥ 0 / 2 := by rel [h']
        _ = 0 := by numbers
    -- ⊢ b > 0
    . calc
        (a + c) / 2 ≥ b / 2 := by addarith [hb]
        _ ≥ 0 / 2 := by rel [h]
        _ = 0 := by numbers
  constructor
  -- ⊢ a + b ≥ 0
  . have H := le_or_gt c 0
    obtain h | h := H
    -- h: c ≤ 0
    . have h' : -c ≥ 0 := by addarith [h]
      calc
        (a + b) / 2 = (a + b + c - c) / 2 := by ring
        _ ≥ (0 - c) / 2 := by rel [h2]
        _ = -c / 2 := by ring
        _ ≥ 0 / 2 := by rel [h']
        _ = 0 := by numbers
    -- ⊢ c > 0
    . calc
        (a + b) / 2 ≥ c / 2 := by addarith [hc]
        _ ≥ 0 / 2 := by rel [h]
        _ = 0 := by numbers
  constructor
  -- a = (a + c) /2 + (a + b) / 2
  -- dead end
  sorry
-/

/-
-- More struggling.
-- Exercise 2.5.9.9.
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  have h1 : a + b + c ≤ 2 * (a + b + c) := by
    calc
      a + b + c ≤ (b + c) + (a + c) + (a + b) := by rel [ha, hb, hc]
      _ = 2 * (a + b + c) := by ring
  have h2 : a + b + c ≥ 0 := by
    have H := le_or_gt (a + b + c) 0
    obtain h | h := H
    -- h: a + b + c ≤ 0
    . calc
        (a + b + c) = 2 * (a + b + c) - (a + b + c) := by ring
        _ ≥ (a + b + c) - (a + b + c) := by rel [h1]
        _ = 0 := by ring
    -- h: a + b + c > 0
    . addarith [h]
  use 0, 0, 0  -- Specific numbers don't work!
  constructor
  numbers -- ⊢ 0 ≥ 0
  constructor
  numbers -- ⊢ 0 ≥ 0
  constructor
  numbers -- ⊢ 0 ≥ 0
  constructor
  -- ⊢ a = 0 + 0
  -- dead end
  sorry
-/

-- Enlightenment :)
-- Exercise 2.5.9.9.
-- First of all, `x, y, z` cannot be some specific real numbers or constants, since
-- `a, b, c` can be any real numbers that satisfy the given hypotheses.
-- Hence, `x, y, z` must be expressed in terms of `a, b, c`. How can we do that?
--  b = x + z => x = b - z, but what is z?
--   a = y + z => z = a - y
--   so, x = b - (a - y) = b - a + y, but what is y?
--     c = x + y => y = c - x
--     so, x = b - a + (c - x) = b - a + c - x
--        2x = b + c - a
--         x = (b + c - a) / 2
-- Then apply similar logic y and z. It's symmetric.
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  -- This is the key insight, or discovery. The rest follows.
  use (b + c - a) / 2, ( a + c - b) / 2, ( a + b - c) / 2
  constructor -- ⊢ (b + c - a) / 2 ≥ 0
  addarith [ha]
  constructor -- ⊢ (a + c - b) / 2 ≥ 0
  addarith [hb]
  constructor -- ⊢ (a + b - c) / 2 ≥ 0
  addarith [hc]
  constructor -- ⊢ a = (a + c - b) / 2 + (a + b - c) / 2
  ring
  constructor -- ⊢ b = (b + c - a) / 2 + (a + b - c) / 2
  ring
  -- ⊢ c = (b + c - a) / 2 + (a + c - b) / 2
  ring
