/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int

/-!
  # 3. [Parity and divisibility](https://hrmacbeth.github.io/math2001/03_Parity_and_Divisibility.html)

  ## 3.1. Definitions; parity
-/

/-!
  ### 3.1.1. Example
-/
example : Odd (7 : ℤ) := by
  -- `dsimp` makes things clearer, but is not necessary.
  dsimp [Odd] -- ⊢ ∃ k, 7 = 2 * k + 1
  use 3
  numbers

/-!
  ### 3.1.2. Example
-/
example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

/-!
  ### 3.1.3. Example
-/
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *  -- the `dsimp` line is not actually needed
  -- Any hypothesis that is odd or even needs to be converted via obtain.
  obtain ⟨k, hk⟩ := hn
  -- A goal with Odd or Even amounts to having an ∃, so a 'use' tactic follows.
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

/-!
  ### 3.1.4. Example
-/
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn  -- hk: n = 2 * k + 1
  -- ⊢ ∃ k, 7 * n - 4 = 2 * k + 1
  -- Note the variable `k` in the goal is different that in `hk`.
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

/-!
  ### 3.1.5. Example
-/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring

/-!
  ### 3.1.6. Example
-/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + (a + b) + (2 * b + 1)
  -- ⊢ 4 * a * b + 2 * (a + b) + 2 * (b + 1) + 1 = 2 * (2 * a * b + (a + b) + (2 * b + 1)) + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + (a + b) + (2 * b + 1)) + 1 := by ring

/-!
  ### 3.1.7. Example
-/
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨k, hk⟩ := hm -- hk: 2 * k + 1
  /-
    Now that we have hk, we can substitute it to the goal, (3 * m - 5).
    Then use some x such that 2 * x would be equal to the goal.
  -/
  use 3 * k - 1
  -- ⊢ 3 * m - 5 = 2 * (3 * k - 1)
  calc
    3 * m - 5 = 3 * (2 * k + 1) - 5 := by rw [hk]
    _ = 2 * (3 * k - 1) := by ring

/-!
  ### 3.1.8. Example
-/
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hn⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc  -- ⊢ n ^ 2 + 2 * n - 5 = 2 * (2 * k ^ 2 + 2 * k - 3) + 1
    n ^ 2 + 2 * n - 5 = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hn]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

/-!
  ### 3.1.9. Example
-/
example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! ### Exercises 3.1.10. -/

-- Exercises 3.1.10.1
example : Odd (-9 : ℤ) := by
  sorry

-- Exercises 3.1.10.2
example : Even (26 : ℤ) := by
  sorry

-- Exercises 3.1.10.3
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  sorry

-- Exercises 3.1.10.4
example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  sorry

-- Exercises 3.1.10.5
example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  sorry

-- Exercises 3.1.10.6
example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  sorry

-- Exercises 3.1.10.7
example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

-- Exercises 3.1.10.8
example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  sorry

-- Exercises 3.1.10.9
example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  sorry

-- Exercises 3.1.10.10
example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  sorry

-- Exercises 3.1.10.11
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry

-- Exercises 3.1.10.12
example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  sorry

-- Exercises 3.1.10.13
example (n : ℤ) : ∃ m ≥ n, Odd m := by
  sorry
-- Exercises 3.1.10.14
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry
