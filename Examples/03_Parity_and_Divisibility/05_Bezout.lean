import Library.Basic

math2001_init

-- Examples 3.5.1
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring

example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5 * a - 3 * n
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

-- Example 3.5.2
example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨m, hm⟩ := h1
  use 2 * m - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * m) - 5 * n := by rw [hm]
    _ = 5 * (2 * m - n) := by ring

-- Example 3.5.3
example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

-- Examples 3.5.4
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨m, hm⟩ := hn
  use 2 * n - m
  calc
    n = 12 * n - 11 * n := by ring
    _ = 12 * n - (6 * m) := by rw [hm]
    _ = 6 * (2 * n - m) := by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨n, hn⟩ := ha
  use 3 * a - 4 * n
  calc
    a = 21 * a - 4 * (5 * a) := by ring
    _ = 21 * a - 4 * (7 * n) := by rw [hn]
    _ = 7 * (3 * a - 4 * n) := by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  use 4 * q - 3 * p
  calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * q) - 27 * n := by rw [hq]
    _ = 28 * (9 * q) - 27 * (7 * p) := by rw [hp]
    _ = 63 * (4 * q - 3 * p) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  use 2 * p - 5 * q
  calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5 * p) - 25 * n := by rw [hp]
    _ = 26 * (5 * p) - 25 * (13 * q) := by rw [hq]
    _ = 65 * (2 * p - 5 * q) := by ring
