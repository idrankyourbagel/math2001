import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

theorem c8 {n : ℕ} (hn : n > 1) : ¬Prime (n ^ 4 + 4) := by
  obtain even_n | odd_n := Nat.even_or_odd n
  . obtain ⟨m, hm⟩ := even_n
    apply not_prime 2 (8 * m ^ 4 + 2)
    . numbers
    . apply ne_of_lt; extra
    . rw [hm]; ring
  . obtain ⟨m, hm⟩ := odd_n
    apply not_prime (4 * m ^ 2 + 8 * m + 5) (4 * m ^ 2 + 1)
    . apply ne_of_gt; extra
    . apply ne_of_lt
      have : m > 0 := by
        have : 1 < 2 * m + 1 := by rw [←hm]; rel [hn]
        addarith [this]
      have : 1 < 4 * m ^ 2 + 1 := by extra
      calc
        4 * m ^ 2 + 8 * m + 5 = 1 * (4 * m ^ 2 + 8 * m + 5) := by ring
        _ < (4 * m ^ 2 + 1) * (4 * m ^ 2 + 8 * m + 5) := by rel [this]
        _ = (2 * m + 1) ^ 4 + 4 := by ring
        _ = _ := by rw [hm]
    . rw [hm]; ring
