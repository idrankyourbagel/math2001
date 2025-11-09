import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 2.4.1
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

-- Example 2.4.2
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 := by apply abs_le_of_sq_le_sq'; addarith [hp]; numbers
  calc
    p ≥ -3 := by rel [hp'.left]
    _ ≥ -5 := by numbers

-- Examples 2.4.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb

-- Example 2.4.4
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  constructor
  . have h2 : a ^ 2 = 0 := by
      apply le_antisymm
      calc
        a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
      extra
    cancel _ at h2
  . have h3 : b ^ 2 = 0 := by
      apply le_antisymm
      calc
        b ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
      extra
    cancel _ at h3

-- Examples 2.4.5
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h1, h2]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  addarith [h2, h1]

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  constructor
  . have : 0 < p + 2 - 2 := by addarith [hp]
    calc
      p ^ 2 = (p + 2 - 2) * (p + 2 - 2) := by ring
      _ ≥ (9 - 2) * (9 - 2) := by rel [hp]
      _ = 49 := by numbers
  . addarith [hp]

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  constructor
  . addarith [h]
  . calc
      3 * a = 3 * (a - 1) + 3 := by ring
      _ ≥ 3 * 5 + 3 := by rel [h]
      _ ≥ 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have :=
    calc
      x = 2 * (x + y) - (x + 2 * y) := by ring
      _ = 2 * 5 - 7 := by rw [h1, h2]
      _ = 3 := by numbers
  constructor
  . apply this
  . rw [this] at h1; addarith [h1]

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h : b = a := by rw [h2] at h1; apply h1
  have :=
    calc
      a * (a - 1) = a * a - a := by ring
      _ = a * b - a := by rw [h]
      _ = a - a := by rw [h1]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at this
  obtain ha | ha := this
  . left
    constructor
    . apply ha
    . rw [h]; apply ha
  . right
    constructor
    . addarith [ha]
    . rw [h]; addarith [ha]
