import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

-- Example 3.2.1
example (a b : ℕ) (h1 : a = 10) (h2 : b = 10): (11 : ℕ) ∣ 88 := by
  use 8; numbers

-- Example 3.2.2
example : (-2 : ℤ) ∣ 6 := by
  use -3; numbers

-- Example 3.2.3
example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2); rw [hk]; ring

-- Example 3.2.4
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  use m ^ 2 * n; rw [hm] at hn; rw [hn]; ring

-- Example 3.2.5
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨c, hc⟩ := h
  use c * y; rw [hc]; ring

-- Example 3.2.6
example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2; constructor; repeat numbers

-- Example 3.2.7
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]

-- Example 3.2.8
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨n, hn⟩ := hab
  rw [hn] at hb; cancel n at hb

-- Examples 3.2.9
example (t : ℤ) : t ∣ 0 := by
  use 0; ring

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor; repeat numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨t, ht⟩ := h
  use t * (3 - 4 * y); rw [ht]; ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  use k * (2 * n ^ 2 + 1); rw [hk]; ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (2 * b ^ 2 - b + 3); rw [hk]; ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  use p ^ 3 * q; rw [hq, hp]; ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨s, hs⟩ := hpq
  obtain ⟨t, ht⟩ := hqr
  use s ^ 2 * t; rw [ht, hs]; ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  . numbers
  . use 7; numbers

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  constructor
  . numbers
  . constructor
    . numbers
    . use 3; numbers
