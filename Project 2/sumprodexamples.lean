import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Gcongr
import Library.Basic

math2001_init

open BigOperators

theorem Finset.sum_Ioc_add'  {M : Type u_3}  [AddCommMonoid M] (f : ℕ → M) (a b c : ℕ) :
∑ x in Ioc a b, f (x + c) = ∑ x in Ioc (a + c) (b + c), f x := by
  rw [← map_add_right_Ioc, sum_map]
  rfl

theorem Finset.sum_Ioc_add  {M : Type u_3}  [AddCommMonoid M] (f : ℕ → M) (a b c : ℕ) :
∑ x in Ioc a b, f (c + x) = ∑ x in Ioc (a + c) (b + c), f x := by
  convert Finset.sum_Ioc_add' f a b c using 2
  rw [add_comm]


-- An inequality example.
example {n : ℕ} (hn : n ≥ 1)
  : ∑ i in Finset.Ioc 0 n, 1 / (i : ℚ) ^ 2 ≤ 2 - 1 / (n : ℚ) := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton]
    numbers
  · -- inductive step
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k)] -- (by addarith [] : 0 ≤ k) also works
    have claim : - 1 / ((k : ℚ) * ↑(k + 1)^2) < 0 := by
      apply div_neg_of_neg_of_pos
      . numbers
      . norm_cast
        calc
          0 < 1 * 1 := by numbers
          _ ≤ k * 1 := by rel [hk]
          _ ≤ k * (k + 1) ^ 2 := by rel [Nat.one_le_pow' 2 k]
    calc
           ∑ k in Finset.Ioc 0 k, 1 / (k : ℚ) ^ 2 + 1 / ↑(k + 1) ^ 2
        ≤ (2 : ℚ) - 1 / ↑k + 1 / ↑(k + 1) ^ 2 := by rel [IH]
      _ = (2 : ℚ) - 1 / (↑k + 1) + (-1 / (↑k * ↑(k + 1)^2)) := by field_simp; ring
      _ ≤ (2 : ℚ) - 1 / (↑k + 1) + 0 := by rel [claim]
      _ = (2 : ℚ) - 1 / (↑k + 1) := by rw [add_zero]


-- A classic result on the sum of the natural numbers from 0 to n.
example (n : ℕ) : ∑ i in Finset.Ioc 0 n, (i : ℚ) = (n * (n + 1) : ℚ) / 2 := by
  simple_induction n with k IH
  · -- base case
    rw [Finset.Ioc_self]
    rw [Finset.sum_empty]
    numbers
  · -- inductive step
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k)]
    rw [IH]
    field_simp -- clear fractions
    norm_cast -- bring everything back to ℕ
    ring


-- An inequality example by manipulating sums instead of using induction
example {n : ℕ} (hn : n ≥ 1) :
  ∑ i in Finset.Ioc 0 n, 1 / ((i : ℚ) * ↑(i + 1)) = ↑n / (n + 1) := by

  obtain ⟨ m, hm ⟩ := Nat.exists_eq_add_of_le' hn
  rw [hm]
  calc
        ∑ i in Finset.Ioc 0 (m + 1), 1 / ((i : ℚ) * ↑(i + 1))
      = ∑ i in Finset.Ioc 0 (m + 1), (1 / (i : ℚ) -  1/ ↑(i + 1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_Ioc] at hk
          obtain ⟨ hl, hr ⟩ := hk
          field_simp
    _ =   ∑ i in Finset.Ioc 0 (m + 1), 1 / (i : ℚ)
        - ∑ i in Finset.Ioc 0 (m + 1), 1/ (↑(i + 1)) := by
          rw [Finset.sum_sub_distrib]
    _ =   ∑ i in Finset.Ioc (0 : ℕ) 1, 1 / (i : ℚ) + ∑ i in Finset.Ioc 1 (m + 1), 1 / ↑i
        - ∑ i in Finset.Ioc 0 (m + 1), 1/ (↑(i + 1)) := by
          rw [Finset.sum_Ioc_consecutive _ (by numbers) (by addarith [])]
    _ = _ := by
          rw [Nat.Ioc_succ_singleton, zero_add, Finset.sum_singleton]
          have :   ∑ i in Finset.Ioc 0 m, 1 / ((@HAdd.hAdd ℕ ℕ ℕ instHAdd i 1) : ℚ)
                 = ∑ i in Finset.Ioc 1 (m + 1), 1 / (i : ℚ) := by
                     rw [Finset.sum_Ioc_add' (fun x ↦ 1 / (x : ℚ)) 0 m]
          rw [← this]
          rw [Finset.sum_Ioc_succ_top (by addarith [hm])]
          rw [tsub_add_eq_tsub_tsub, add_sub_assoc, sub_self]
          field_simp


-- An example of strong induction in the way the textbook does.
theorem my_inequality (n : ℕ) (x : ℕ → ℤ)
  : |∑ i in Finset.range n, x i| ≤ ∑ i in Finset.range n, |x i| := by

  have two_terms (a b : ℤ) : |a + b| ≤ |a| + |b| := by
    have h1 : |a| + |b| = |(|a| + |b|)| := by
      have : 0 ≤ |a| + |b| := by
        have ha : 0 ≤ |a| := by apply abs_nonneg
        have hb : 0 ≤ |b| := by apply abs_nonneg
        addarith [ha, hb]
      rw [abs_eq_self.mpr this]
    rw [h1]
    rw [← sq_le_sq]
    calc
      (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
      _ = |a| ^ 2 + |b| ^ 2 + 2 * (a * b) := by rw [sq_abs, sq_abs]
      _ ≤ |a| ^ 2 + |b| ^ 2 + 2 * (|a| * |b|) := by
        have : a * b ≤ |a| * |b| := by
          calc
            a * b ≤ |a * b| := by apply le_abs_self
            _ = |a| * |b| := by apply abs_mul
        rel [this]
      _ = _ := by ring

  match n with
  | 0 =>
    rfl
  | 1 =>
    rw [Finset.range_one]
    rw [Finset.sum_singleton, Finset.sum_singleton]
  | 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.range_zero, Finset.sum_empty, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.range_zero, Finset.sum_empty, zero_add]
    apply two_terms
  | k + 3 =>
    calc
          |∑ i in Finset.range (k + 3), x i|
        = |∑ i in Finset.range (k + 2), x i + x (k + 2)| := by
            rw [Finset.sum_range_succ]
      _ ≤ |∑ i in Finset.range (k + 2), x i| + |x (k + 2)| := by
            apply two_terms
      _ ≤ ∑ i in Finset.range (k + 2), |x i| + |x (k + 2)| := by
            rel [my_inequality (k + 2) x]
      _ = _ := by
            have : k + 3 = (k + 2) + 1 := by ring
            rw [this]
            rw [Finset.sum_range_succ _ (k + 2)]


-- An example involving a sum of binomial coefficients
example {n k : ℕ}
  : ∑ i in Finset.range (k + 1), (n + i).choose i = (n + k + 1).choose k := by
  simple_induction k with m IH
  . rw [Finset.range_one]
    rw [Finset.sum_singleton]
    rw [Nat.choose_zero_right, Nat.choose_zero_right]
  . rw [Finset.sum_range_succ, IH]
    calc
          (n + m + 1).choose m + (n + (m + 1)).choose (m + 1)
        = (n + m + 1).choose m + (n + m + 1).choose m.succ := by rfl
      _ = (n + m + 1).succ.choose m.succ := by
            rw [← Nat.choose_succ_succ]
