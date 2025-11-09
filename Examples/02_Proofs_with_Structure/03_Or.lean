import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 2.3.1
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  . rw [hx]; ring
  . rw [hy]; ring

-- Example 2.3.2
example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  . apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  . apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

-- Example 2.3.3
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers

-- Example 2.3.4
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h | h := h2
  . left; addarith [h]
  . right; addarith [h]

-- Example 2.3.5
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]

-- Examples 2.3.6
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hx | hx := h
  . rw [hx]; numbers
  . rw [hx]; numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hx := h
  . rw [hx]; numbers
  . rw [hx]; numbers

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain ht | ht := h
  . rw [ht]; numbers
  . rw [ht]; numbers

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  . rw [hx]; ring
  . rw [hy]; ring

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  . left; rw [h]; ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  . right; addarith [h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  . left
    calc
      x < (2 * x + 1) / 2 := by addarith []
      _ = y / 2 := by rw [h]

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have :=
    calc
      (x - 1) * (x + 3) = x ^ 2 + 2 * x - 3 := by ring
      _ = 0 := by rw [hx]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  obtain h | h := this
  . right; addarith [h]
  . left; addarith [h]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have :=
    calc
      (a - 2 * b) * (a - b) = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
      _ = _ := by rw [hab]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  obtain h | h := this
  . right; addarith [h]
  . left; addarith [h]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have :=
    calc
      t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
      _ = t ^ 3 - t ^ 3 := by rw [ht]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  obtain h | h := this
  . right; cancel _ at h
  . left; addarith [h]

example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain hn | hn := hn
  . apply ne_of_lt
    calc
      n ^ 2 ≤ 2 ^ 2 := by rel [hn]
      _ < 7 := by numbers
  . apply ne_of_gt
    calc
      n ^ 2 ≥ 3 ^ 2 := by rel [hn]
      _ > 7 := by numbers

example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hx | hx := hx
  . apply ne_of_lt
    calc
      2 * x ≤ 2 * 1 := by rel [hx]
      _ < 3 := by numbers
  . apply ne_of_gt
    calc
      3 < 2 * 2 := by numbers
      _ ≤ 2 * x := by rel [hx]

example {t : ℤ} : 5 * t ≠ 18 := by
  have ht := le_or_succ_le t 3
  obtain ht | ht := ht
  . apply ne_of_lt
    calc
      5 * t ≤ 5 * 3 := by rel [ht]
      _ < 18 := by numbers
  . apply ne_of_gt
    calc
      18 < 5 * 4 := by numbers
      _ ≤ 5 * t := by rel [ht]

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hm | hm := hm
  . apply ne_of_lt
    calc
      m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [hm]
      _ < 46 := by numbers
  . apply ne_of_gt
    calc
      46 < 6 ^ 2 + 4 * 6 := by numbers
      _ ≤ m ^ 2 + 4 * m := by rel [hm]
