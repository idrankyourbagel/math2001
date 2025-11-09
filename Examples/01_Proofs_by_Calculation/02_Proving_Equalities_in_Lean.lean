import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by numbers

-- Example 1.2.2
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * 3 := by rw [h2, h1]
    _ = -7 := by numbers

-- Example 1.2.3
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) : (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2 = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.2.4
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) : d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = a * d * f - d * e * b := by ring
    _ = b * c * f - c * f * b := by rw [h1, h2]
    _ = 0 := by ring
