/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int

-- Example 4.5.1
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this

-- Example 4.5.2
example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h := calc
      15 = 3 * 5 := by numbers
      _ ≤ 3 * k := by rel [h5]
      _ = 13 := by rw [hk]
    numbers at h

-- Example 4.5.3
example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H

-- Example 4.5.4
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro hn
  obtain ⟨n, hn⟩ := hn
  have := le_or_succ_le n 1
  obtain h | h := this
  . interval_cases n
    . numbers at hn
    . numbers at hn
  . have := calc
      2 = n ^ 2 := by rw [hn]
      _ ≥ 2 ^ 2 := by rel [h]
      _ > 2 := by numbers
    numbers at this

-- Examples 4.5.5
example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction

example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h := calc
      1 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 0 [ZMOD 2] := h2
    numbers at h
  . intro h
    rw [Int.even_iff_modEq] at h
    mod_cases n % 2
    . contradiction
    . rw [Int.odd_iff_modEq]
      exact H

-- Example 4.5.6
example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have : n ^ 2 ≡ 1 ^ 2 [ZMOD 3] := by apply Int.ModEq.pow; exact hn;
    have : 1 ≡ 2 [ZMOD 3] := calc
      1 = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [this]
      _ ≡ 2 [ZMOD 3] := h
    numbers at this
  · have : n ^ 2 ≡ 2 ^ 2 [ZMOD 3] := by apply Int.ModEq.pow at hn; exact hn
    have := calc
      2 ≡ n ^ 2 [ZMOD 3] := by rel [h]
      _ ≡ 2 ^ 2 [ZMOD 3] := by rel [this]
      _ = 1 * 3 + 1 := by numbers
      _ ≡ 1 [ZMOD 3] := by extra
    numbers at this

-- Example 4.5.7
example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction

-- Example 4.5.8
example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  sorry

-- Examples 4.5.9
example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · sorry
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · sorry
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction

example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · sorry
  · sorry
  · sorry
  · sorry

-- Examples 4.5.10

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry

example : ¬ Int.Even 7 := by
  sorry

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  sorry

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  sorry

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

example : ¬ Prime 1 := by
  sorry

example : Prime 97 := by
  sorry
