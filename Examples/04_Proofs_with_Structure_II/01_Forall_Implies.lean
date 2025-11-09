import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Example 4.1.1
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers

-- Example 4.1.2
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2

-- Example 4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain ha | hb := h
  . calc
      a = 2 * a - a := by ring
      _ ≤ 2 * ((a + b) / 2) - a := by rel [ha]
      _ = b := by ring
  . calc
      b = 2 * b - b := by ring
      _ ≥ 2 * ((a + b) / 2) - b := by rel [hb]
      _ = a := by ring

-- Example 4.1.4
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
(hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) : a = b := by
  apply le_antisymm
  · apply hb2; apply ha1
  · apply ha2; apply hb1

-- Example 4.1.5
example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1; intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring

-- Example 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3; intro x y h
  have :=
    calc
      (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
      _ = 2 * (x ^ 2 + y ^ 2) := by ring
      _ ≤ 2 * 4 := by rel [h]
      _ ≤ 3 ^ 2 := by numbers
  apply abs_le_of_sq_le_sq' at this
  have : -3 ≤ x + y ∧ x + y ≤ 3 := by
    apply this; numbers
  obtain ⟨h, h'⟩ := this
  apply h

-- Example 4.1.7
example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  use 5; intro n hn
  calc
    n ^ 3 = (n - 1) * n ^ 2 + n ^ 2 := by ring
    _ ≥ (5 - 1) * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 25 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by addarith []

-- Example 4.1.8
example : Prime 2 := by
  constructor
  · numbers
  . intro m hmp
    have hp : 0 < 2 := by numbers
    have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
    have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
    interval_cases m
    · left; numbers
    · right; numbers

-- Example 4.1.9
example : ¬Prime 6 := by
  apply not_prime 2 3; repeat numbers

-- Examples 4.1.10
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by ring

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h1 : 3 ∣ n := by apply hn; repeat numbers
  have h2 : 5 ∣ n := by apply hn; repeat numbers
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  use 2 * k - 3 * l
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * k) - 9 * n := by rw [hk]
    _ = 10 * (3 * k) - 9 * (5 * l) := by rw [hl]
    _ = 15 * (2 * k - 3 * l) := by ring

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0; intro m; extra

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0; intro b; use b + 1; addarith []

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 7; intro n hn
  calc
    n ^ 3 + 3 * n = n * n ^ 2 + 3 * n := by ring
    _ ≥ 7 * n ^ 2 + 3 * 7 := by rel [hn]
    _ ≥ 7 * n ^ 2 + 12 := by addarith []

example : ¬(Prime 45) := by
  apply not_prime 3 15; repeat numbers
