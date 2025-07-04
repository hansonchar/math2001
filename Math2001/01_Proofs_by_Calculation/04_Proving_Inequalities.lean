/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.4: Proving inequalities -/


-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h2, h1]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤ -2 + y := by rel [h2]
    _ ≤ -2 + (x + 5) := by rel [h1]
    _ ≤ -2 + (-2 + 5) := by rel [h2]
    _ < 2 := by numbers

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h5, h4]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9, h8]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by numbers

/-
  Note:

  The example above has a small subtlety.  On seeing the hypothesis , you might be tempted to “substitute” it directly into the expression `t ^ 2 - 3 * t - 17`, but that would not be valid.

  See https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id41
-/

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n := by ring
    _ ≥ 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ ≥ 2 * n + 3 * 5 := by rel [hn]
    _ > 2 * n + 11 := by norm_num

/-
  Kyle Miller: Yes, using a more powerful tactic can do that, however: the book never uses
  `norm_num`. The only real mention of it is in the very last chapter,
  [Transitioning to mainstream](https://hrmacbeth.github.io/math2001/Mainstream_Lean.html) Lean.
  You shouldn't consider `norm_num` to be a solution here.

  [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.E2.9C.94.20Example.201.2E4.2E6.20of.20The.20Mechanics.20of.20Proof/with/525445003).
-/

-- Example 1.4.6 take 2 using `extra`:
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    -- n ^ 2 > n ^ 2 - 4 := by extra -- <= failed but why?
    n ^ 2 = n * n := by ring
    _ ≥ 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ ≥ 2 * n + 3 * 5 := by rel [hn]
    _ = 2 * n + 11 + 4 := by ring
    _ > 2 * n + 11 := by extra

/-
  Kenny Lau: probably because they aren't "differing by some neutral quantity",
  try making the LHS n^2-0 first to a mathematician n^2 and n^2-0 are obviously the same,
  but not to a computer
-/

-- This works:
-- n ^ 2 = n ^ 2 - 0 := by ring
-- _  > n ^ 2 - 4 := by extra

-- This would also work:
-- n ^ 2 = n ^ 2 + 0 := by ring
-- _ ≥ 0 := by extra

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]

-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = a + (a + 2 * b - a) / 2 := by ring  -- (1)
    _ ≥ a + (4 - a) / 2 := by rel [h2]
    _ = (4 + a) / 2 := by ring
    _ ≥ (4 + 3) / 2 := by rel [h1]              -- (4)
    _ = 3 + 1 / 2 := by ring
    _ ≥ 3 := by extra

/-!
  Remarks:
  * `a ≥ 3` means `a` can be easily converted from to a constant so that's not a problem.
  * We somehow need to have the term `a + 2 * b`, so that led us to the formation of (1).
  * Once we get to (4), we need to massage it into something we can make use of `extra`.
-/

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x ^ 2 * (x - 8) + 2 * x := by ring -- this is the key step
    _ ≥ 9 ^ 2 * (9 - 8) + 2 * 9 := by rel [hx]
    _ ≥ 3 := by numbers

/-!
  Remark: The hypothesis `hx` has `x` in the first degree, and it's much easier to reason
  about the inequality by factoring out the square.
-/

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
    n ^ 4 - 2 * n ^ 2 = n ^ 2 * (n * n - 2) := by ring  -- (1)
    _ ≥ n ^ 2 * (10 * n - 2) := by rel [hn]
    _ = n ^ 2 * (3 * n + 7 * n - 2) := by ring
    _ ≥ n ^ 2 * (3 * n + 7 * 10 - 2) := by rel [hn]     -- (2)
    _ = 3 * n ^ 3 + n ^ 2 * 68 := by ring
    _ ≥ 3 * n ^ 3 + 10 ^ 2 * 68 := by rel [hn]          -- (3)
    _ > 3 * n ^ 3 := by extra

/-!
  Remark. The key is to factor out $n^2$ as (1), and then massage $n^2 - 2$ into the form of
  $a * n + b$ for some constants $a, b$ as in (2).
  From there we want to arrive at the form of $3 * n^3 + c$ for some constant $c$, as in (3),
  and we are all set.
-/

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n ^ 2 - 2 * n + 3 = n * n - 2 * n + 3 := by ring
    _ ≥ 5 * n - 2 * n + 3 := by rel [h1]
    _ = 3 * n + 3 := by ring
    _ ≥ 3 * 5 + 3 := by rel [h1]
    _ > 14 := by numbers

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring
    _ ≥ - 1 := by extra

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 2 * a * b := by extra
