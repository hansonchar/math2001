/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/-!
  ## 3.4. Modular arithmetic: calculations
-/

/-!
  ### 3.4.1. Example

  It’s easy to write a Lean tactic which checks the correctness of a class of statement. The author has done exactly this, updating tactic `rel` to cover this kind of statement. We won’t discuss tactic-writing in this book, but effectively, the tactic now throws the lemmas `Int.ModEq.add`, `Int.ModEq.neg`, `Int.ModEq.sub`, `Int.ModEq.mul`, `Int.ModEq.pow`, `Int.ModEq.refl` and the provided hypotheses at the statement until (a) the goal is solved or (b) none of these lemmas apply any more. And that’s exactly what we’re doing in our heads when we check the paper statement of the problem.
-/
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]

/-!
  ### 3.4.2. Example

  From now on, we will solve more interesting modular arithmetic problems, dealing with steps like Example 3.3.11 in a single line.
-/
example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    -- Notice the use of `≡` here.
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    -- Notice the use of `=` here.
    _ = 2 + 5 * 8 := by numbers
    -- Interesting use of `by extra`.
    _ ≡ 2 [ZMOD 5] := by extra

/-!
  ### 3.4.3. Example
-/
example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra -- Another example of using `extra`.

/-!
  ### 3.4.4. Example

  Interesting example of using `mod_cases`.
-/
example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  -- hx : x ≡ 0 [ZMOD 3]
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  -- hx : x ≡ 1 [ZMOD 3]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  -- hx : x ≡ 2 [ZMOD 3]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    -- Notice this repeated pattern of re-expressing in a specific form of addition.
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! ### 3.4.5. Exercises -/

-- Exercise 3.4.5.1
example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
  sorry

-- Exercise 3.4.5.2
example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
  sorry

-- Exercise 3.4.5.3
example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] :=
  sorry

-- Exercise 3.4.5.4
example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  sorry

-- Exercise 3.4.5.5
example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  sorry

-- Exercise 3.4.5.6
example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  sorry

-- Exercise 3.4.5.7
example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  sorry
