import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 2.5.1
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  rw [hb]; extra

-- Example 2.5.2
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < -x * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt; apply hxt'
  . have :=
      calc
        0 < -x * t := by addarith [hxt]
        _ = x * -t := by ring
    have hx' : 0 ≤ x := by rel [hx]
    cancel x at this
    addarith [this]

-- Example 2.5.3
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7; numbers

-- Example 2.5.4
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1; extra

-- Example 2.5.5
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5; numbers

-- Example 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
 use a + 1, a; ring

-- Example 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  . calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  . calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]

-- Example 2.5.8
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  . numbers
  . constructor
    . numbers
    . constructor; repeat numbers

-- Examples 2.5.9
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3; numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2, 9; numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.1
  constructor; repeat numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3; numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 0.5
  calc
    (x + 0.5) ^ 2 = x ^ 2 + 0.25 + x := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have ha :=
    calc
      0 = a + t - (a + t) := by ring
      _ < a + t - (a * t + 1) := by rel [ha]
      _ = (a - 1) * (1 - t) := by ring
  obtain ha' | ha' := by apply le_or_gt 0 (a - 1)
  . cancel (a - 1) at ha
    apply ne_of_lt
    addarith [ha]
  . have ha :=
      calc
        0 < (a - 1) * (1 - t) := by rel [ha]
        _ = (1 - a) * (t - 1) := by ring
    have ha' : 0 < (1 - a) := by addarith [ha']
    cancel (1 - a) at ha
    apply ne_of_gt
    addarith [ha]

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  obtain ha' | ha' := by apply le_or_succ_le a 2
  . apply ne_of_lt
    calc
      m = 2 * a := by rw [ha]
      _ ≤ 2 * 2 := by rel [ha']
      _ < 5 := by numbers
  . apply ne_of_gt
    calc
      m = 2 * a := by rw [ha]
      _ ≥ 2 * 3 := by rel [ha']
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain hn | hn := by apply le_or_gt 0 n
  . use n + 2
    calc
      2 * (n + 2) ^ 3 = 2 * n ^ 3 + 11 * n ^ 2 + 22 * n + 9 + n ^ 2 + 2 * n + 7 := by ring
      _ ≥ n ^ 2 + 2 * n + 7 := by extra
      _ = n * (n + 2) + 7 := by ring
  . use 2
    calc
      2 * 2 ^ 3 ≥ 0 + 0 + 7 := by numbers
      _ ≥ n + n + 7 := by rel [hn]
      _ = n * 2 + 7 := by ring

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  constructor
  . calc
      (b + c - a) / 2 ≥ (b + c - (b + c)) / 2 := by rel [ha]
      _ = 0 := by ring
  . constructor
    . calc
        (a + c - b) / 2 ≥ (a + c - (a + c)) / 2 := by rel [hb]
        _ = 0 := by ring
    . constructor
      . calc
          (a + b - c) / 2 ≥ (a + b - (a + b)) / 2 := by rel [hc]
          _ = 0 := by ring
      . constructor
        . ring
        . constructor; repeat ring
