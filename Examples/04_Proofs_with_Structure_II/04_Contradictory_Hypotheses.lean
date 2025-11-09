import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

-- Example 4.4.1
example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hy | hy := le_or_lt y 0
  · have : ¬0 < x * y := by
      apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hy]
    contradiction
  · apply hy

-- Example 4.4.2
example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
    calc
      7 = t := by addarith [h]
      _ < 3 := h2
  numbers at H

-- Example 4.4.3
example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) : n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · left; apply h
  · have H :=
      calc
        0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
        _ = 1 ^ 2 + 1 + 1 := by numbers
        _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
        _ ≡ 1 [ZMOD 3] := hn
    numbers at H
  · right; apply h

-- Examples 4.4.4
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp
  . intro m hmp
    have hp' : 0 < p := by extra
    have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
    obtain hm | hm_left := eq_or_lt_of_le h1m
    · left; rw [hm]
    . have : m ≤ p := by apply Nat.le_of_dvd; apply hp'; apply hmp
      obtain HM | HM_left := eq_or_lt_of_le this
      . right; apply HM
      . left
        apply H at HM_left
        contradiction
        apply hm_left

example : Prime 5 := by
  apply prime_test
  · numbers
  . intro m hm_left hm_right
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

-- Example 4.4.5
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain ha' | ha' := by apply le_or_succ_le a 2
  . obtain hb' | hb' := by apply le_or_succ_le b 1
    . have : c ^ 2 < 3 ^ 2 :=
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha', hb']
          _ < 3 ^ 2 := by numbers
      cancel _ at this
      interval_cases a <;>
        interval_cases b <;>
          interval_cases c <;>
            numbers at h_pyth
    . have H :=
        calc
          b ^ 2 < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := by rw [h_pyth]
      cancel _ at H
      have H : b + 1 ≤ c := by addarith [H]
      have H' :=
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha']
          _ = b ^ 2 + 2 * 2 := by ring
          _ ≤ b ^ 2 + 2 * b := by rel [hb']
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      cancel _ at H'
      have :=
        calc
          b + 1 ≤ c := H
          _ < b + 1 := H'
      apply ne_of_lt at this
      contradiction
  . apply ha'

-- Examples 4.4.6
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  obtain hxy | hxy := le_or_gt y x
  . apply hxy
  . have : y ^ n > x ^ n := by rel [hxy]
    have :=
      calc
        y ^ n ≤ x ^ n := h
        _ < y ^ n := this
    apply ne_of_lt at this
    contradiction

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases n % 5
  . obtain ⟨m, hm⟩ := H
    have :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ = (n - 0) ^ 2 := by ring
        _ = (5 * m) ^ 2 := by rw [hm]
        _ = 5 * (5 * m ^ 2) := by ring
        _ ≡ 0 [ZMOD 5] := by extra
    numbers at this
  . obtain ⟨m, hm⟩ := H
    have :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ = (n - 1) ^ 2 + 2 * (n - 1) + 1 := by ring
        _ = (5 * m) ^ 2 + 2 * (5 * m) + 1 := by rw [hm]
        _ = 5 * (5 * m ^ 2 + 2 * m) + 1 := by ring
        _ ≡ 1 [ZMOD 5] := by extra
    numbers at this
  . left; apply H
  . right; apply H
  . obtain ⟨m, hm⟩ := H
    have :=
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ = (n - 4) ^ 2 + 8 * (n - 4) + 16 := by ring
        _ = (5 * m) ^ 2 + 8 * (5 * m) + 16 := by rw [hm]
        _ = 5 * (5 * m ^ 2 + 8 * m + 3) + 1 := by ring
        _ ≡ 1 [ZMOD 5] := by extra
    numbers at this

example : Prime 7 := by
  apply prime_test
  . numbers
  . intro m hm_left hm_right
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    . use 3; constructor <;> numbers
    . use 2; constructor <;> numbers
    repeat use 1; constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3 | h3 := h3
  . have h2 : 3 < x + 2 := by addarith [h2]
    rw [h3] at h2; numbers at h2
  . addarith [h3]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain hp | hp := Nat.even_or_odd p
  . left; obtain ⟨q, hq⟩ := hp
    rw [hq] at h
    obtain hq' | hq' := le_or_succ_le q 1
    . interval_cases q
      . have : ¬Prime (2 * 0) := by
          dsimp [Prime]; push_neg; left; numbers
        contradiction
      . addarith [hq]
    . have : ¬Prime (2 * q) := by
        apply not_prime q 2
        . apply ne_of_gt; addarith [hq']
        . have :=
            calc
              q < q + 2 := by extra
              _ ≤ q + q := by rel [hq']
              _ = 2 * q := by ring
          apply ne_of_lt
          apply this
        . ring
      contradiction
  . right; apply hp
