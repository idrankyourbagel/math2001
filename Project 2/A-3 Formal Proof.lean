import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring
import Library.Basic

theorem a3 {n : ℕ} : (2 * n).choose n * (3 * n + 1).sqrt ≤ 4 ^ n  := by
  simple_induction n with k IH
  . rw [Nat.choose_zero_right]
    rw [Nat.sqrt_one]
    numbers
  . sorry
