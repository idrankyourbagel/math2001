import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 2.1.1
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, this]
    _ = 9 := by ring

-- Example 2.1.2
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have :=
    calc
      m + 3 ≤ 2 * n - 1 := by rel [h1]
      _ ≤ 2 * 5 - 1 := by rel [h2]
      _ = 9 := by numbers
  addarith [this]

-- Example 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4]
    _ = 3 := by ring

-- Example 2.1.4
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have :=
    calc
      t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]
  cancel t at this
  addarith [this]

-- Example 2.1.5
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have :=
    calc
      a ^ 2 = b ^ 2 + 1 := by rw [h1]
      _ ≥ 1 := by extra
      _ = 1 ^ 2 := by ring
  cancel 2 at this

-- Example 2.1.6
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have : x ≤ -1 := by addarith [hx]
  calc
    y ≥ 3 - 2 * x := by addarith [hy]
    _ ≥ 3 - 2 * -1 := by rel [this]
    _ > 3 := by numbers

-- Example 2.1.7
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ a + b := by addarith [h1]
  have : 0 ≤ b - a := by addarith [h2]
  calc
    _ = a ^ 2 + 0 * (b - a) := by ring
    _ ≤ a ^ 2 + (a + b) * (b - a) := by rel [h3]
    _ = b ^ 2 := by ring

-- Example 2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have : 0 ≤ b - a := by addarith [h]
  calc
    a ^ 3 ≤ a ^ 3 + (b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2) / 4 := by extra
    _ = b ^ 3 := by ring

-- Examples 2.1.9
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have :=
    calc
      x * (x + 2) = x ^ 2 - 4 + 2 * (x + 2) := by ring
      _ = 2 * (x + 2) := by addarith [h1]
  cancel (x + 2) at this

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have :=
    calc
      (n - 2) ^ 2 = n ^ 2 - 4 * n + 4 := by ring
      _ = 0 := by addarith [hn]
  cancel _ at this
  addarith [this]

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have : 0 < x * y := by addarith [h]
  cancel x at this
  calc
    y = 1 * y := by ring
    _ ≤ x * y := by rel [h2]
    _ = 1 := by rw [h]
