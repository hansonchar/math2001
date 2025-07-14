/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

/-!
  ## 3.5. Bézout’s identity
-/

/-!
  ### 3.5.1. Example
-/
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring

/-!
  Such a problem will typically have many possible solutions. Here is another solution.
-/
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5 * a - 3 * n
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

/-!
  ### 3.5.2. Example
-/
example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  use 2 * x - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * x) - 5 * n := by rw [hx]
    _ = 5 * (2 * x - n) := by ring

/-!
  ### 3.5.3. Example
-/
example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! ### 3.5.4. Exercises -/

-- Exercise 3.5.4.1.
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 2 * n - a
  calc
    -- We want to have some `(11 * n)` and the other term divisible by 6.
    n = 12 * n - (11 * n) := by ring
    _ = 12 * n - 6 * a := by rw [ha]
    _ = 6 * (2 * n - a) := by ring

-- Exercise 3.5.4.2.
example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨x, hx⟩ := ha
  use 3 * x - 2 * a
  calc
    a = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * x) - 14 * a := by rw [hx]
    _ = 7 * (3 * x - 2 * a) := by ring

-- Exercise 3.5.4.3.
example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 4 * b - 3 * a
  calc
    -- We want two terms of $n$ that differ by one.
    -- One has a factor being the multiple of 7, and the other a multiple of 9.
    -- (Note that 7 and 9 are read off from `ha` and `hb`.)
    -- This allows us to expand both terms into a multiple of 63 when replaced with `a` and `b`.
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * b) - 27 * n := by rw [hb]
    _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
    _ = 63 * (4 * b - 3 * a) := by ring

-- Exercise 3.5.4.4.
example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 2 * a - 5 * b
  calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5 * a) - 25 * n := by rw [ha]
    _ = 26 * (5 * a) - 25 * (13 * b) := by rw [hb]
    _ = 65 * (2 * a - 5 * b) := by ring
