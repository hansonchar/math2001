/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

/-!
  ## 3.3. Modular arithmetic: theory

  Definition: The integers $a$ and $b$ are congruent modulo $n$, if $n ∣ (a-b)$.
-/

/-!
  ### 3.3.1. Example
-/
example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

/-!
  ### 3.3.2. Example
-/
example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

/-!
  ### 3.3.3. Example

  Lemma (addition rule for mudular arithmetric).
-/
theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

/-!
  ### 3.3.4. Exercise

  Lemma (subtraction rule for mudular arithmetric).
-/
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x - y
  calc
    a - c - (b - d) = a - b - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

/-!
  ### 3.3.5. Exercise

  Lemma (negative rule for mudular arithmetric).
-/
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨c, hc⟩ := h1
  use -c
  calc
    -a - -b = -(a - b) := by ring
    _ = -(n * c) := by rw [hc]
    _ = n * -c := by ring

/-!
  ### 3.3.6. Example

  Lemma (multiplication rule for mudular arithmetric).
-/
theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

/-!
  ### 3.3.7. Example

  Warning: There is no “division rule” for modular arithmetic!

  It is possible to have integers $a, b, c, d$ and $n$ with $a ≡ b mod n$ and $c ≡ d$ mod $n$, but
  $a/c ¬≡ b/d$ mod $n$.
-/

/-!
  ### 3.3.8. Example

  Lemma (squaring rule for mudular arithmetric).
-/
theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring

/-!
  ### 3.3.9. Exercise

  Cubing rule for modular arithmetic.
-/
theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = n * x * (a ^ 2 + a * b + b ^ 2) := by rw [hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring

/-!
  Power fule for modular arithmetic.

  In fact the same is true for any power, although we don’t yet have the tools to prove it.
  We’ll come back to this later in the book, in Example 6.1.3.
-/
theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  sorry -- we'll prove this later in the book

/-!
  ### 3.3.10. Example

  Reflexivity rule for modular arithmetic.
-/
theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring

/-!
  ### 3.3.11. Example

  We could solve this by working directly from the definition, which is rather painful.
-/
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2) =
        (a - 2) * (b ^ 2 + a * b + 2 * b + 3) :=
      by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring

/-!
  Or, better, we can solve this by applying the right combination of the lemmas we already proved, in the right order. This requires much less thinking.
-/
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  --  ⊢ a * b ^ 2 + a ^ 2 * b ≡ 2 * b ^ 2 + 2 ^ 2 * b [ZMOD 4]
  . apply Int.ModEq.add
    -- ⊢ a * b ^ 2 ≡ 2 * b ^ 2 [ZMOD 4]
    . apply Int.ModEq.mul
      -- ⊢ a ≡ 2 [ZMOD 4]
      . apply ha
      -- ⊢ b ^ 2 ≡ b ^ 2 [ZMOD 4]
      . apply Int.ModEq.refl
    -- ⊢ a ^ 2 * b ≡ 2 ^ 2 * b [ZMOD 4]
    . apply Int.ModEq.mul
      -- ⊢ a ^ 2 ≡ 2 ^ 2 [ZMOD 4]
      . apply Int.ModEq.pow
        -- ⊢ a ≡ 2 [ZMOD 4]
        apply ha
      -- ⊢ b ≡ b [ZMOD 4]
      . apply Int.ModEq.refl
  -- ⊢ 3 * a ≡ 3 * 2 [ZMOD 4]
  . apply Int.ModEq.mul
    -- ⊢ 3 ≡ 3 [ZMOD 4]
    . apply Int.ModEq.refl
    -- ⊢ a ≡ 2 [ZMOD 4]
    . apply ha

/-! 3.3.12. Exercises -/


-- Exercise 3.3.12.1
example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  calc
    34 - 104 = 5 * -14 := by ring

/-!
  #### Exercise 3.3.12.2

  Symmetry rule for modular arithmetic.
-/
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use -x
  calc
    b - a = - (a - b) := by ring
    _ = - (n * x) := by rw [hx]
    _ = n * (-x) := by ring

/-!
  #### Exercise 3.3.12.3

  Transitivity rule for modular arithmetic.
-/
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a - c = a - b + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

-- Exercise 3.3.12.4
example : a + n * c ≡ a [ZMOD n] := by
  use c
  calc
    a + n * c - a = n * c := by ring

-- Exercise 3.3.12.6
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  . apply Int.ModEq.mul
    . apply Int.ModEq.refl
    . apply h
  . apply Int.ModEq.refl

-- Exercise 3.3.12.7
example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.sub
  . apply Int.ModEq.mul
    . apply Int.ModEq.refl
    . apply h
  . apply Int.ModEq.refl

-- Exercise 3.3.12.8
example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply hb
  apply Int.ModEq.pow_three
  apply hb
  apply Int.ModEq.refl
