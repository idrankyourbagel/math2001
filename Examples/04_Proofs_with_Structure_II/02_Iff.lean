import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

-- Example 4.2.1
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc
      a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ 2 := by addarith [h]
  · intro h
    calc
      3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers

-- Example 4.2.2
example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc
      5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring

-- Example 4.2.3
theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    use k; addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k; addarith [hk]

-- Example 4.2.4
theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    use k; addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k; addarith [hk]

-- Example 4.2.5
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have : (x - 2) * (x + 3) = 0 :=
      calc
        (x - 2) * (x + 3) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [h]
    apply eq_zero_or_eq_zero_of_mul_eq_zero at this
    obtain hx | hx := this
    . right; addarith [hx]
    . left; addarith [hx]
  . intro h
    obtain hx | hx := h
    repeat rw [hx]; numbers

-- Example 4.2.6
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have :=
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * -1 + 5 := by rel [h]
        _ = 1 ^ 2 := by numbers
    apply abs_le_of_sq_le_sq' at this
    obtain ⟨H, H'⟩ := by apply this; numbers
    have ha :=
      calc
        2 * a = 2 * a - 5 + 5 := by ring
        _ ≥ -1 + 5 := by rel [H]
        _ = 2 * 2 := by numbers
    cancel 2 at ha
    have ha' :=
      calc
      2 * a = 2 * a - 5 + 5 := by ring
      _ ≤ 1 + 5 := by rel [H']
      _ = 2 * 3 := by numbers
    cancel 2 at ha'
    interval_cases a
    . left; numbers
    . right; numbers
  . intro h
    obtain ha | ha := h
    repeat rw [ha]; numbers

-- Examples 4.2.7
example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc
      (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn | hn := hn2
  . use 2; addarith [hn]
  . use 3; addarith [hn]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc
      (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1
  obtain hn | hn := hn1
  . use 2; addarith [hn]
  . use 3; addarith [hn]

-- Example 4.2.8
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra

-- Example 4.2.9
example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left; rw [Int.even_iff_modEq]; apply hn
  · right; rw [Int.odd_iff_modEq]; apply hn

-- Examples 4.2.10
example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  . intro h
    have : 2 * x = 2 * 6 := by addarith [h]
    cancel 2 at this
  . intro h; rw [h]; numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  . intro h
    constructor
    . obtain ⟨m, hm⟩ := h
      use 9 * m
      calc
        n = 63 * m := hm
        _ = 7 * (9 * m) := by ring
    . obtain ⟨m, hm⟩ := h
      use 7 * m
      calc
        n = 63 * m := hm
        _ = 9 * (7 * m) := by ring
  . intro h
    obtain ⟨hn, hn'⟩ := h
    obtain ⟨p, hp⟩ := hn
    obtain ⟨q, hq⟩ := hn'
    use 4 * q - 3 * p
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * q) - 27 * n := by rw [hq]
      _ = 28 * (9 * q) - 27 * (7 * p) := by rw [hp]
      _ = 63 * (4 * q - 3 * p) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  repeat
    intro h
    obtain ⟨k, hk⟩ := h
    use k; addarith [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [Int.dvd_iff_modEq]
  have : 2 * b ^ 3 - b ^ 2 + 3 * b ≡ 0 [ZMOD a] := by
    obtain ⟨k, hk⟩ := hab
    use k * (2 * b ^ 2 - b + 3)
    calc
      _ = b * (2 * b ^ 2 - b + 3) := by ring
      _ = a * k * (2 * b ^ 2 - b + 3) := by rw [hk]
      _ = _ := by ring
  apply this

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have : k ^ 2 < 3 ^ 2 := by addarith [h]
    have : k < 3 := by cancel _ at this
    interval_cases k
    . left; numbers
    . right; left; numbers
    . right; right; numbers
  . intro h
    obtain hk | hk | hk := h
    repeat rw [hk]; numbers
