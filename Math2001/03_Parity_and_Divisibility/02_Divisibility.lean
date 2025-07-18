/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

/-!
  ## 3.2. Divisibility

  ### 3.2.1. Example
-/
example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)] -- to unfold the definition; optional.
  use 8
  numbers

/-!
  ### 3.2.2. Example
-/
example : (-2 : ℤ) ∣ 6 := by
  use -3
  numbers

/-!
  ### 3.2.3. Example
-/
example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring

/-!
  ### 3.2.4. Example
-/
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use x ^ 2 * y
  calc
    c = b ^ 2 * y := hy
    _ = (a * x) ^ 2 * y := by rw [hx]
    _ = a ^ 2 * (x ^ 2 * y) := by ring

/-!
  ### 3.2.5. Example
-/
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨t, ht⟩ := h
  use y * t
  calc
    z = x * y * t := ht
    _ = x * (y * t) := by ring

/-!
  ### 3.2.6. Example

  You might wonder how to show that a number is not divisible by another number. A convenient test here is a theorem which we will prove later in the book, in Example 4.5.8: if an integer $a$ is strictly between two consecutive multiples of an integer $b$, then it is not a multiple of $b$. More formally, if there exists an integer $q$ such that $bq < a < b(q+1)$, then $a$ is not a multiple of $b$. Here is an example applying this test:
-/
example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt  -- Criterion for an integer not to divide another.
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`

/-!
  ### 3.2.7. Example

  Let $a$ and $b$ be natural numbers, with $b$ positive, and suppose that $a$ divides $b$. Show that $a ≤ b$.

  This lemma is available in the main Lean library under the name `Nat.le_of_dvd`.
-/
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  -- Interesting that H1 is constructed directly without stating what it is up front.
  have H1 :=      -- H1 : 0 < a * k
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1  -- H1 : 0 < k
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]

/-!
  ### 3.2.8. Example

  Let $a$ and $b$ be natural numbers, with $b$ positive, and suppose that $a$ divides $b$. Show that $a$ is positive.

  This lemma is also available in the main Lean library, under the name `Nat.pos_of_dvd_of_pos`.
-/
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨c, hc⟩ := hab
  have H := calc
    0 < b := hb
    _ = a * c := hc
  cancel c at H

/-! ### 3.2.9 Exercises -/

-- Exercise 3.2.9.1
example (t : ℤ) : t ∣ 0 := by
  use 0 -- ⊢ 0 = t * 0
  ring  -- Interesting we can just say `ring` in lieu of the more verbose form below.
  -- calc
  --    0 = t * 0 := by ring

-- Exercise 3.2.9.2
example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt -- Criterion for an integer not to divide another.
  use -4  -- ⊢ 3 * -4 < -10 ∧ -10 < 3 * (-4 + 1)
  constructor
  -- ⊢ 3 * -4 < -10
  . numbers
  -- ⊢ -10 < 3 * (-4 + 1)
  . numbers

-- Exercise 3.2.9.3
example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  use 3 * k - 4 * x * k ^ 2 -- Trick: add this `use` statement as the last step after finishing the `calc`
  calc
    3 * y - 4 * y ^ 2 = 3 * (x * k) - 4 * (x * k)^2 := by rw [hk]
    _ = x * (3 * k - 4 * x * k ^ 2) := by ring

-- Exercise 3.2.9.4
example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  use 2 * m ^ 2 * k ^ 3 + k
  calc
    2 * n ^ 3 + n = 2 * (m * k) ^ 3 + (m * k) := by rw [hk]
    _ = m * (2 * m ^ 2 * k ^ 3 + k) := by ring

-- Exercise 3.2.9.5
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨c, hc⟩ := hab
  use 2 * a ^ 2 * c ^ 3 - a * c ^ 2 + 3 * c
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * c) ^ 3 - (a * c) ^ 2 + 3 * (a * c) := by rw [hc]
    _ = a * (2 * a ^ 2 * c ^ 3 - a * c ^ 2 + 3 * c) := by ring

-- Exercise 3.2.9.6
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x ^ 3 * y
  calc
    m = l ^ 3 * y := hy
    _ = (k * x) ^ 3 * y := by rw [hx]
    _ = k ^ 3 * (x ^ 3 * y) := by ring

-- Exercise 3.2.9.7
example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨x, hx⟩ := hpq
  obtain ⟨y, hy⟩ := hqr
  use x ^ 2 * y
  calc
    r = q ^ 2 * y := hy
    _ = (p ^ 3 * x) ^ 2 * y := by rw [hx]
    _ = p ^ 6 * (x ^ 2 * y) := by ring

-- Exercise 3.2.9.8
example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6 -- ⊢ 0 < 6 ∧ 9 ∣ 2 ^ 6 - 1
  constructor
  -- ⊢ 0 < 6
  . numbers
  -- ⊢ 9 ∣ 2 ^ 6 - 1
  . use 7
    numbers

-- Exercise 3.2.9.9
example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1    -- ⊢ 0 < 1 ∧ 1 < 2 ∧ 2 - 1 ∣ 2 + 1
  constructor -- ⊢ 0 < 1
  . numbers
  constructor -- ⊢ 1 < 2
  . numbers
          -- ⊢ 2 - 1 ∣ 2 + 1
  . use 3 -- ⊢ 2 + 1 = (2 - 1) * 3
    calc
      2 + 1 = (2 - 1) * 3 := by numbers
