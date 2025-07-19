/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
  # 4. Proofs with structure, II
-/

/-!
  ## 4.1. “For all” and implication

  ### 4.1.1. Example

  Let $a$ be a real number and suppose that for all real numbers, it is true that $a ≤ x^2-2x$.
  Show that $a ≤ -1$.

  To use a hypothesis with a universal quantifier, you may want to "specialize" its use to one particular variable. For example, in the solution below, we use the special case of the hypothesis in which $x$ is set to $1$.
-/
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers

/-!
  ### 4.1.2. Example

  Let $n$ be a natural number which is a factor of every natural number $m$. Show that $n=1$.
-/
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2

/-!
  ### 4.1.3. Example

  Let $a$ and $b$ be real numbers and suppose that every real number $x$ is either at least $a$ or at most $b$. Show that $a ≤ b$.
-/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  -- A clever selection of (a + b) / 2!
  have H : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h1 | h1 := H
  -- h1: (a + b) / 2 ≥ a
  -- |- a ≤ b
  -- The solution opens up by simply considering `b` on the lhs instead of `a`!
  . have hb : b ≥ a := by
      calc
        b = (a + b) / 2 * 2 - a := by ring
        _ ≥ a * 2 - a := by rel [h1]
        _ = a := by ring
    apply hb
  -- h1: (a + b) / 2 ≤ b
  -- |- a ≤ b
  . calc
      a = (a + b) / 2 * 2 - b := by ring
      _ ≤ b * 2 - b := by rel [h1]
      _ = b := by ring

/-!
  ### 4.1.4. Example

  Let $a$ be real number whose square is at most 2, and which is greater than or equal to any real number whose square is at most 2. Let $b$ be another real number with the same two properties. Prove that $a=b$.
-/
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  -- Given all the hypothesis involve ≤ or ≥, but the goal involves =,
  -- it makes sense to split the goal also into ≤ and ≥.
  apply le_antisymm -- Split = into two cases of ≤ and ≥.
  -- ⊢ a ≤ b
  -- This changes the goal to be the antecedent of the implication hb2.
  · apply hb2 -- ⊢ a ^ 2 ≤ 2
    apply ha1
  -- ⊢ b ≤ a
  -- This changes the goal to be the antecedent of the implication ha2.
  · apply ha2 -- ⊢ b ^ 2 ≤ 2
    exact hb1

/-!
  ### 4.1.5. Example

  Show that there exists a real number $b$ such that for every real number $x$, it is true that $b ≤ x^2 - 2x$.
-/
example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x -- introduces a particular, arbitrary real number `x`, so this changes the goal
  -- from:  ⊢ ∀ (x : ℝ), -1 ≤ x ^ 2 - 2 * x
  --   to:  x : ℝ
  --        ⊢ -1 ≤ x ^ 2 - 2 * x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring

/-!
  ### 4.1.6. Example
-/
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  sorry

/-!
  ### 4.1.7. Example
-/
example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra

/-!
  ### 4.1.8. Example
-/
example : Prime 2 := by
  constructor
  · numbers -- show `2 ≤ 2`
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`

/-!
  ### 4.1.9. Example
-/
example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! ### 4.1.10. Exercises -/

-- Exercise 4.1.10.1
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  sorry

-- Exercise 4.1.10.2
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

-- Exercise 4.1.10.3
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

-- Exercise 4.1.10.4
example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

-- Exercise 4.1.10.5
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

-- Exercise 4.1.10.6
example : ¬(Prime 45) := by
  sorry
