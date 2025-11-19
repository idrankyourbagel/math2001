import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Library.Basic

math2001_init

open BigOperators

def Fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => Fib (n + 1) + Fib n

theorem c1 {n : ℕ} : ∑ k in Finset.Ico 0 n, Fib (2 * k + 1) = Fib (2 *  n) := by
  two_step_induction n with m IH1 IH2
  · rw [Finset.Ico_self] -- Range is empty
    rw [Finset.sum_empty] -- Empty sum = 0
    dsimp [Fib] -- 0 = Fib 0
  · rw [Nat.Ico_succ_singleton] -- Range is one
    rw [Finset.sum_singleton]
    dsimp [Fib] -- Fib 1 = Fib 2 (since Fib (0 + 2) = Fib 1 + Fib 0 = Fib 1)
  · rw [Nat.Ico_zero_eq_range]
    rw [Finset.sum_range_succ]
    rw [←Nat.Ico_zero_eq_range]
    rw [IH2]
    dsimp [Fib]
    ring
