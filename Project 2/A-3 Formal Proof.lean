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

lemma h4 {n : ℕ} : (n + 1) * (n.factorial * n.factorial) ∣ 2 * ((2 * n + 1) * (2 * n).factorial) := by sorry

lemma h5 {n : ℕ} : (n + 1) ^ 2 * Nat.factorial n ^ 2 * Nat.factorial n ^ 2 ∣ 4 * (2 * n + 1) ^ 2 * Nat.factorial (2 * n) ^ 2 := by sorry


lemma bulkCalculation {n : ℕ} : ((2 * (n + 1)).choose (n + 1)) ^ 2 * (3 * (n + 1) + 1) = ((4 * (2 * n + 1) ^ 2 * (3 * n + 4)) / ((n + 1) ^ 2 * (3 * n + 1))) * (((2 * n).choose n) ^ 2 * (3 * n + 1)) := by calc
      ((2 * (n + 1)).choose (n + 1)) ^ 2 * (3 * (n + 1) + 1)
    = ((2 * (n + 1)).factorial / ((n + 1).factorial * (2 * (n + 1) - (n + 1)).factorial)) ^ 2
      * (3 * (n + 1) + 1) := by rw [Nat.choose_eq_factorial_div_factorial]; exact h1

  _ = ((2 * n + 2).factorial / ((n + 1).factorial * (n + 1).factorial)) ^ 2 * (3 * n + 4) := by rw [h2, h3]; ring

  _ = ((2 * n + 2) * (2 * n + 1).factorial / ((n + 1).factorial * (n + 1).factorial)) ^ 2 * (3 * n + 4) := by
        rw [Nat.factorial_succ]

  _ = ((2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) /
      ((n + 1).factorial * (n + 1).factorial)) ^ 2 * (3 * n + 4) := by rw [Nat.factorial_succ]

  _ = ((2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) /
      ((n + 1) * n.factorial * (n + 1).factorial)) ^ 2 * (3 * n + 4) := by rw [Nat.factorial_succ]

  _ = ((2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) /
      ((n + 1) * n.factorial * ((n + 1) * n.factorial))) ^ 2 * (3 * n + 4) := by rw [Nat.factorial_succ]

  _ = ((n + 1) * (2 * ((2 * n + 1) * (2 * n).factorial)) /
      ((n + 1) * ((n + 1) * (n.factorial * n.factorial)))) ^ 2 * (3 * n + 4) := by ring

  _ = (2 * ((2 * n + 1) * (2 * n).factorial) / ((n + 1) * (n.factorial * n.factorial))) ^ 2
      * (3 * n + 4) := by rw [Nat.mul_div_mul_left]; extra

  _ = (2 * ((2 * n + 1) * (2 * n).factorial)) ^ 2 / ((n + 1) * (n.factorial * n.factorial)) ^ 2
      * (3 * n + 4) := by rw [Nat.div_pow]; exact h4

  _ = (2 ^ 2 * ((2 * n + 1) * (2 * n).factorial) ^ 2) / ((n + 1) * (n.factorial * n.factorial)) ^ 2
      * (3 * n + 4) := by rw [Nat.mul_pow]

  _ = (2 ^ 2 * ((2 * n + 1) ^ 2 * (2 * n).factorial ^ 2)) / ((n + 1) * (n.factorial * n.factorial)) ^ 2
      * (3 * n + 4) := by rw [Nat.mul_pow]

  _ = (2 ^ 2 * ((2 * n + 1) ^ 2 * (2 * n).factorial ^ 2)) / ((n + 1) ^ 2 * (n.factorial * n.factorial) ^ 2)
      * (3 * n + 4) := by rw [Nat.mul_pow]

  _ = (2 ^ 2 * ((2 * n + 1) ^ 2 * (2 * n).factorial ^ 2)) / ((n + 1) ^ 2 * (n.factorial ^ 2 * n.factorial ^ 2))
      * (3 * n + 4) := by rw [Nat.mul_pow]

  _ = (4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2) / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2))
      * 1 * (3 * n + 4) := by ring

  _ = (4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2) / ((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2)
      * ((3 * n + 1) / (3 * n + 1)) * (3 * n + 4) := by rw [Nat.div_self]; extra

  _ = (4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2) * (3 * n + 1)
      / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2) * (3 * n + 1))
      * (3 * n + 4) := by rw [←Nat.mul_div_mul_comm_of_dvd_dvd]; exact h5; use 1; ring

  _ = ((4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2) * (3 * n + 1)
      / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2) * (3 * n + 1)))
      * (3 * n + 4) := by ring

  _ = (3 * n + 4) * ((4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2 * (3 * n + 1))
      / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2) * (3 * n + 1))) := by rw [Nat.mul_comm]

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2 * (3 * n + 1))
      / ((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2 * (3 * n + 1)) := by rw [←Nat.mul_div_assoc]; sorry

  _ = ((3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1))) * ((2 * n).factorial ^ 2)
      / (((n + 1) ^ 2 * (3 * n + 1)) * (n.factorial ^ 2 * n.factorial ^ 2)) := by ring

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / (n.factorial ^ 2 * n.factorial ^ 2)) := by
        rw [Nat.mul_div_mul_comm_of_dvd_dvd]; sorry; sorry

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / (n.factorial ^ 2 * (2 * n - n).factorial ^ 2)) := by rw [h2]

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / ((n.factorial * (2 * n - n).factorial) ^ 2)) := by rw [Nat.mul_pow];

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial / (n.factorial * (2 * n - n).factorial)) ^ 2 := by rw [Nat.div_pow]; sorry

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).choose n) ^ 2 := by rw [←Nat.choose_eq_factorial_div_factorial]; exact h1

  _ = (3 * n + 1) * (4 * (3 * n + 4) * (2 * n + 1) ^ 2) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).choose n) ^ 2 := by ring

  _ = (3 * n + 1) * ((4 * (3 * n + 4) * (2 * n + 1) ^ 2) / ((n + 1) ^ 2 * (3 * n + 1)))
      * ((2 * n).choose n) ^ 2 := by rw [Nat.mul_div_assoc]; sorry

  _ = ((4 * (2 * n + 1) ^ 2 * (3 * n + 4)) / ((n + 1) ^ 2 * (3 * n + 1)))
      * (((2 * n).choose n) ^ 2 * (3 * n + 1)) := by ring



theorem a3 {n : ℕ} : ((2 * n).choose n) ^ 2 * (3 * n + 1) ≤ 4 ^ (2 * n) := by
  simple_induction n with k IH
  . dsimp [Nat.choose]; numbers
  . calc

      ((2 * (k + 1)).choose (k + 1)) ^ 2 * (3 * (k + 1) + 1)

      _ = ((4 * (2 * k + 1) ^ 2 * (3 * k + 4)) / ((k + 1) ^ 2 * (3 * k + 1)))
          * (((2 * k).choose k) ^ 2 * (3 * k + 1)) := by rw [bulkCalculation]

      _ ≤ ((4 * (2 * k + 1) ^ 2 * (3 * k + 4)) / ((k + 1) ^ 2 * (3 * k + 1))) * 4 ^ (2 * k) := by rel [IH]

      _ = (48 * k ^ 3 + 112 * k ^ 2 + 76 * k + 16) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k) := by ring

      _ ≤ (48 * k ^ 3 + 112 * k ^ 2 + 76 * k + 16) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k)
        + 4 * k / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k) := by extra

      _ = (48 * k ^ 3 + 112 * k ^ 2 + 80 * k + 16) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k) := by sorry
          -- This result cannot be proven with Nat.div, since it is literally false for most values of k. Of course, this works under Rat.div, since it is actually true for rationals.

      _ = 4 * 4 * (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1)
          * 4 ^ (2 * k) := by ring

      _ = 4 * 4 * ((3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1))
          * 4 ^ (2 * k) := by rw [Nat.mul_div_assoc]; use 1; ring

      _ = 4 * 4 * 1 * 4 ^ (2 * k) := by rw [Nat.div_self]; extra

      _ = 4 ^ (2 * (k + 1)) := by ring
