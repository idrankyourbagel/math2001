import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

math2001_init

namespace Int

-- Example 4.3.1
example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2; constructor
  · numbers
  . intro y hy
    calc
      y = (3 * y + 1 - 1) / 3 := by ring
      _ = (7 - 1) / 3 := by rw [hy]
      _ = 2 := by numbers

-- Example 4.3.2
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2; constructor
  . intro a ha ha'
    have : (a - 2) ^ 2 ≤ 1 ^ 2 := by
      apply sq_le_sq'; addarith [ha]; addarith [ha']
    addarith [this]
  . intro x hx
    apply le_antisymm
    . have : (x - 1) ^ 2 ≤ 1 ^ 2 := by
        calc
          (x - 1) ^ 2 = (1 - x) ^ 2 := by ring
          _ ≤ 1 := by apply hx; numbers; numbers
          _ = 1 ^ 2 := by numbers
      obtain ⟨h, h'⟩ := by apply abs_le_of_sq_le_sq' at this; apply this; numbers
      addarith [h']
    . have : (x - 3) ^ 2 ≤ 1 ^ 2 := by
        calc
          (x - 3) ^ 2 = (3 - x) ^ 2 := by ring
          _ ≤ 1 := by apply hx; numbers; numbers
          _ = 1 ^ 2 := by numbers
      obtain ⟨h, h'⟩ := by apply abs_le_of_sq_le_sq' at this; apply this; numbers
      addarith [h]

-- Example 4.3.3
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, h1, h2⟩ := hx
  have : -a = a := by
    apply h2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := h1
  have :=
    calc
      a = (a + a) / 2 := by ring
      _ = (a + -a) / 2 := by rw [this]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [h1]
    _ = 0 ^ 2 := by rw [this]
    _ = 0 := by ring

-- Example 4.3.4
example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

-- Examples 4.3.5
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  . numbers
  . intro x hx
    calc
      x = (4 * x - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw [hx]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  . intro a; extra
  . intro n hn
    have : n ≤ 0 := by apply hn
    rw [←Nat.le_zero_eq]
    exact this

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  . constructor
    . numbers
    . constructor
      . numbers
      . calc
          11 = 2 + 3 * 3 := by numbers
          _ ≡ 2 [ZMOD 3] := by extra
  . intro y hy
    obtain ⟨h1, h2, h3⟩ := hy
    interval_cases y
    . apply Int.not_dvd_of_exists_lt_and_lt at h3
      contradiction
      use 3; constructor <;> numbers
    . apply Int.not_dvd_of_exists_lt_and_lt at h3
      contradiction
      use 3; constructor <;> numbers
    . numbers
