import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Init.Data.Nat
import Library.Basic


lemma h1 {n : ℕ} : n + 1 ≤ 2 * (n + 1) := calc
  n + 1 ≤ n + 1 + n + 1 := by extra
  _ = 2 * (n + 1) := by ring

lemma h2 {n : ℕ} : 2 * n - n = n := calc
  2 * n - n = n + n - n := by ring
  _ = n + (n - n) := by rw [Nat.add_sub_assoc]; extra
  _ = n + 0 := by rw [Nat.sub_self]
  _ = n := by rw [Nat.add_zero]

lemma h3 {n : ℕ} : 2 * (n + 1) = 2 * n + 2 := by ring

lemma h4 {n : ℕ} : 3 * (n + 1) + 1 = 3 * n + 4 := by ring

lemma h5 {n : ℕ} : (k + 1) * n.factorial ^ 2 ∣ 2 * (2 * n + 1) * (2 * n).factorial := by sorry

lemma mul_div_mul_comm_actual {a b c d : ℕ} (hba : b ∣ a) (hdc : d ∣ c) : a * c / (b * d) = a / b * (c / d) := sorry


theorem a3 {n : ℕ} : ((2 * n).choose n) ^ 2 * (3 * n + 1) ≤ 4 ^ (2 * n) := by
  simple_induction n with k IH
  . rw [Nat.choose_zero_right (2 * 0)]; numbers
  . calc
      ((2 * (k + 1)).choose (k + 1)) ^ 2 * (3 * (k + 1) + 1)
        = ((2 * (k + 1)).factorial / ((k + 1).factorial * (2 * (k + 1) - (k + 1)).factorial)) ^ 2
          * (3 * (k + 1) + 1) := by rw [Nat.choose_eq_factorial_div_factorial]; exact h1
      _ = ((2 * k + 2).factorial / ((k + 1).factorial * (k + 1).factorial)) ^ 2 * (3 * k + 4) := by rw [h2, h3, h4]
      _ = (((2 * k + 2) * (2 * k + 1).factorial) / ((k + 1).factorial * (k + 1).factorial)) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]
      _ = (((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial)) / ((k + 1).factorial * (k + 1).factorial)) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]
      _ = (((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial)) / ((k + 1) * k.factorial * (k + 1).factorial)) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]
      _ = (((2 * k + 2) * ((2 * k + 1) * (2 * k).factorial)) / ((k + 1) * k.factorial * ((k + 1) * k.factorial))) ^ 2
          * (3 * k + 4) := by rw [Nat.factorial_succ]
      _ = (2 * (2 * k + 1) * (2 * k).factorial * (k + 1) / ((k + 1) * k.factorial * k.factorial * (k + 1))) ^ 2
          * 1 * (3 * k + 4) := by ring
      _ = (2 * (2 * k + 1) * (2 * k).factorial * (k + 1) / ((k + 1) * k.factorial * k.factorial * (k + 1))) ^ 2
          * 1 * ((3 * k + 4) / 1) := by rw [Nat.div_one]
      _ = (2 * (2 * k + 1) * (2 * k).factorial * (k + 1) / ((k + 1) * k.factorial * k.factorial * (k + 1))) ^ 2
          * ((3 * k + 1) / (3 * k + 1)) * ((3 * k + 4) / 1) := by rw [Nat.div_self]; extra



      _ ≤ 4 ^ (2 * (k + 1)) := by sorry
