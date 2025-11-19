import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Init.Data.Nat
import Library.Basic
import Library.Tactic.ModEq

lemma h1 {n : ℕ} : n ≤ 2 * n := calc
  n ≤ n + n := by extra
  _ = _ := by ring

lemma h2 {n : ℕ} : 2 * n - n = n := calc
  2 * n - n = n + n - n := by ring
  _ = n := by rw [Nat.add_sub_cancel]

lemma h3 {n : ℕ} : 2 * (n + 1) = 2 * n + 2 := by ring



theorem a3 {n : ℕ} : ((2 * n).choose n) ^ 2 * (3 * n + 1) ≤ 4 ^ (2 * n) := by
  simple_induction n with k IH
  . dsimp [Nat.choose]; numbers
  . calc
      ((2 * (k + 1)).choose (k + 1)) ^ 2 * (3 * (k + 1) + 1)

        = ((2 * (k + 1)).factorial / ((k + 1).factorial * (2 * (k + 1) - (k + 1)).factorial)) ^ 2
          * (3 * (k + 1) + 1) := by rw [Nat.choose_eq_factorial_div_factorial]; exact h1

      _ = ((2 * k + 2).factorial / ((k + 1).factorial * (k + 1).factorial)) ^ 2 * (3 * k + 4)
          := by rw [h2, h3]; ring

      _ = ((2 * k + 2) * (2 * k + 1).factorial / ((k + 1).factorial * (k + 1).factorial)) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]

      _ = ((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) / ((k + 1).factorial * (k + 1).factorial)) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]

      _ = ((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) /
          ((k + 1) * k.factorial * (k + 1).factorial)) ^ 2 * (3 * k + 4) := by rw [Nat.factorial_succ]

      _ = ((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) /
          ((k + 1) * k.factorial * ((k + 1) * k.factorial))) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]

      _ = (((2 * k + 2) * (2 * k + 1)) * (2 * k).factorial /
          (((k + 1) * (k + 1)) * (k.factorial * k.factorial))) ^ 2 * (3 * k + 4) := by ring

      _ = (((2 * k + 2) * (2 * k + 1)) / ((k + 1) * (k + 1)) *
          ((2 * k).factorial / (k.factorial * k.factorial))) ^ 2
          * (3 * k + 4) := by sorry -- Not sure why rw [Nat.mul_div_mul_comm] doesn't work here.

      _ = (((2 * k + 2) * (2 * k + 1)) / ((k + 1) * (k + 1)) *
          ((2 * k).factorial / (k.factorial * (2 * k - k).factorial))) ^ 2
          * (3 * k + 4) := by rw [h2]

      _ = (((2 * k + 2) * (2 * k + 1)) / ((k + 1) * (k + 1)) *
          (2 * k).choose k) ^ 2 * (3 * k + 4) := by rw [Nat.choose_eq_factorial_div_factorial]; exact h1

      _ = ((k + 1) * (2 * (2 * k + 1)) / ((k + 1) * (k + 1))) ^ 2 * ((2 * k).choose k) ^ 2
          * (3 * k + 4) := by ring

      _ = ((k + 1) / (k + 1) * ((2 * (2 * k + 1)) / (k + 1))) ^ 2 * ((2 * k).choose k) ^ 2
          * (3 * k + 4) := by sorry -- Again, rw [Nat.mul_div_mul_comm] should work.

      _ = (1 * ((2 * (2 * k + 1) / (k + 1)))) ^ 2 * ((2 * k).choose k) ^ 2
          * (3 * k + 4) := by rw [Nat.div_self]; extra

      _ = (2 * (2 * k + 1) / (k + 1)) ^ 2 * ((2 * k).choose k) ^ 2 * (3 * k + 4) * 1 := by ring

      _ = (2 * (2 * k + 1) / (k + 1)) ^ 2 * ((2 * k).choose k) ^ 2
          * (3 * k + 4) * ((3 * k + 1) / (3 * k + 1)) := by rw [Nat.div_self]; extra

      _ = (2 * (2 * k + 1) / (k + 1)) ^ 2 * ((2 * k).choose k) ^ 2
          * (3 * k + 4) * (3 * k + 1) / (3 * k + 1) := by rw [←Nat.mul_div_assoc]; use 1; ring

      _ = ((2 * k).choose k) ^ 2 * (3 * k + 1) * (2 * (2 * k + 1) / (k + 1)) ^ 2
          * (3 * k + 4) / (3 * k + 1) := by ring

      _ ≤ 4 ^ (2 * k) * (2 * (2 * k + 1) / (k + 1)) ^ 2 * (3 * k + 4) / (3 * k + 1) := by rel [IH]

      _ = 4 ^ (2 * k) * 2 ^ 2 * ((2 * k + 1) ^ 2 * (3 * k + 4)) / ((k + 1) ^ 2 * (3 * k + 1)) := by sorry
          -- Many things happened here that are not possible to prove using Nat.div.

      _ = 4 ^ (2 * k) * 4 * (12 * k ^ 3 + 28 * k ^ 2 + 19 * k + 4)
          / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) := by ring

      _ ≤ 4 ^ (2 * k) * 4 * (12 * k ^ 3 + 28 * k ^ 2 + 19 * k + 4)
          / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) + k / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) := by extra

      _ ≤ 4 ^ (2 * k) * 4 * (12 * k ^ 3 + 28 * k ^ 2 + 19 * k + 4 + k)
          / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) := by sorry
          -- rel [Nat.add_div_le_add_div] should work here.

      _ = 4 ^ (2 * k) * 4 * 4 * (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1)
          / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) := by ring

      _ = 4 ^ (2 * k) * 4 * 4 * ((3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1)
          / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1)) := by rw [Nat.mul_div_assoc]; use 1; ring

      _ = 4 ^ (2 * k) * 4 * 4 * 1 := by rw [Nat.div_self]; extra

      _ = 4 ^ (2 * (k + 1)) := by ring
