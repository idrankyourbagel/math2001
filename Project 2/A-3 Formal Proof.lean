import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Cast.Basic
import Init.Data.Nat
import Library.Basic

def qchoose: ℕ → ℕ → ℚ
  | _, 0 => (1 : ℚ)
  | 0, _ + 1 => (0 : ℚ)
  | n + 1, k + 1 => (Nat.choose n k + Nat.choose n (k + 1) : ℚ)

theorem a3 {n : ℕ} : ((2 * n).choose n) ^ 2 * (3 * n + 1) ≤ 4 ^ (2 * n) := by
  simple_induction n with k IH
  . rw [Nat.choose_zero_right (2 * 0)]; numbers
  . sorry
