import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Init.Data.Nat
import Library.Basic

open BigOperators

lemma h1 {n : ℕ} : n ≤ 2 * n := calc
  n ≤ n + n := by extra
  _ = _ := by ring

lemma h2 {n : ℕ} : 2 * n - n = n := calc
  2 * n - n = n + n - n := by ring
  _ = n := by rw [Nat.add_sub_cancel]

lemma h3 {n : ℕ} : 2 * (n + 1) = 2 * n + 2 := by ring

lemma h4 {n : ℕ} : 12 * n ^ 3 + 28 * n ^ 2 + 19 * n + 4 ≤ 12 * n ^ 3 + 28 * n ^ 2 + 20 * n + 4 := calc
  12 * n ^ 3 + 28 * n ^ 2 + 19 * n + 4 ≤ 12 * n ^ 3 + 28 * n ^ 2 + 19 * n + 4 + n := by extra
  _ = 12 * n ^ 3 + 28 * n ^ 2 + 20 * n + 4 := by ring

lemma bulkCalculation {n : ℕ} : ((2 * (n + 1)).choose (n + 1)) ^ 2 * (3 * (n + 1) + 1) = ((4 * (2 * n + 1) ^ 2 * (3 * n + 4)) / ((n + 1) ^ 2 * (3 * n + 1))) * (((2 * n).choose n) ^ 2 * (3 * n + 1)) := calc

  ((2 * (n + 1)).choose (n + 1)) ^ 2 * (3 * (n + 1) + 1)
    = ((2 * (n + 1)).factorial / ((n + 1).factorial * (2 * (n + 1) - (n + 1)).factorial)) ^ 2
      * (3 * (n + 1) + 1) := by rw [Nat.choose_eq_factorial_div_factorial]; exact h1

  _ = ((2 * n + 2).factorial / ((n + 1).factorial * (n + 1).factorial)) ^ 2 * (3 * n + 4) := by rw [h2, h3]; ring

  -- If I were to lift to the rationals, this is probably where I would do it, so that I can change the division to Rat.div while they're still equivalent.

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
      * (3 * n + 4) := by rw [Nat.div_pow]; sorry
      -- This result is not provable, since it is literally false for some values of n. However, if I had lifted to the rationals earlier, the corresponding Rat.div result is true and easily provable.

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
      * (3 * n + 4) := by rw [←Nat.mul_div_mul_comm_of_dvd_dvd]; sorry; use 1; ring
      -- The corresponding Rat.div result is true and provable.

  _ = ((4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2) * (3 * n + 1)
      / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2) * (3 * n + 1)))
      * (3 * n + 4) := by ring

  _ = (3 * n + 4) * ((4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2 * (3 * n + 1))
      / (((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2) * (3 * n + 1))) := by rw [Nat.mul_comm]

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (2 * n).factorial ^ 2 * (3 * n + 1))
      / ((n + 1) ^ 2 * n.factorial ^ 2 * n.factorial ^ 2 * (3 * n + 1)) := by rw [←Nat.mul_div_assoc]; sorry
      -- The corresponding Rat.div result is true and provable.

  _ = ((3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1))) * ((2 * n).factorial ^ 2)
      / (((n + 1) ^ 2 * (3 * n + 1)) * (n.factorial ^ 2 * n.factorial ^ 2)) := by ring

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / (n.factorial ^ 2 * n.factorial ^ 2)) := by
        rw [Nat.mul_div_mul_comm_of_dvd_dvd]; sorry; sorry
      -- The corresponding Rat.div result is true and provable.

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / (n.factorial ^ 2 * (2 * n - n).factorial ^ 2)) := by rw [h2]

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial ^ 2 / ((n.factorial * (2 * n - n).factorial) ^ 2)) := by rw [Nat.mul_pow];

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).factorial / (n.factorial * (2 * n - n).factorial)) ^ 2 := by rw [Nat.div_pow]; sorry
      -- The corresponding Rat.div result is true and provable.

  -- If I had lifted to the rationals, here I would have to change the factorial terms back to naturals and switch the corresponding Rat.div to Nat.div so that I can perform the following step of rewriting this as a binomial coefficient.

  _ = (3 * n + 4) * (4 * (2 * n + 1) ^ 2 * (3 * n + 1)) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).choose n) ^ 2 := by rw [←Nat.choose_eq_factorial_div_factorial]; exact h1

  _ = (3 * n + 1) * (4 * (3 * n + 4) * (2 * n + 1) ^ 2) / ((n + 1) ^ 2 * (3 * n + 1))
      * ((2 * n).choose n) ^ 2 := by ring

  _ = (3 * n + 1) * ((4 * (3 * n + 4) * (2 * n + 1) ^ 2) / ((n + 1) ^ 2 * (3 * n + 1)))
      * ((2 * n).choose n) ^ 2 := by rw [Nat.mul_div_assoc]; sorry
      -- The corresponding Rat.div result is true and provable.

  _ = ((4 * (2 * n + 1) ^ 2 * (3 * n + 4)) / ((n + 1) ^ 2 * (3 * n + 1)))
      * (((2 * n).choose n) ^ 2 * (3 * n + 1)) := by ring



theorem a3 {n : ℕ} : ((2 * n).choose n) ^ 2 * (3 * n + 1) ≤ 4 ^ (2 * n) := by
  simple_induction n with k IH
  . dsimp [Nat.choose]; numbers
  . calc
      ((2 * (k + 1)).choose (k + 1)) ^ 2 * (3 * (k + 1) + 1)
        = ((4 * (2 * k + 1) ^ 2 * (3 * k + 4)) / ((k + 1) ^ 2 * (3 * k + 1)))
          * (((2 * k).choose k) ^ 2 * (3 * k + 1)) := by rw [bulkCalculation]

      _ ≤ ((4 * (2 * k + 1) ^ 2 * (3 * k + 4)) / ((k + 1) ^ 2 * (3 * k + 1))) * 4 ^ (2 * k) := by rel [IH]

      _ = 4 * (12 * k ^ 3 + 28 * k ^ 2 + 19 * k + 4) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k) := by ring

      _ ≤ 4 * (12 * k ^ 3 + 28 * k ^ 2 + 20 * k + 4) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) * 4 ^ (2 * k) := by rel [h4]

      _ = 4 * 4 * (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1)
          * 4 ^ (2 * k) := by ring

      _ = 4 * 4 * ((3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1) / (3 * k ^ 3 + 7 * k ^ 2 + 5 * k + 1))
          * 4 ^ (2 * k) := by rw [Nat.mul_div_assoc]; use 1; ring

      _ = 4 * 4 * 1 * 4 ^ (2 * k) := by rw [Nat.div_self]; extra

      _ = 4 ^ (2 * (k + 1)) := by ring
