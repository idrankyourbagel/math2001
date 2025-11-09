import Library.Basic

math2001_init

open Int

-- Example 3.1.1
example : Odd (7 : ℤ) := by
  use 3; numbers

-- Example 3.1.2
example : Odd (-3 : ℤ) := by
  use -2; numbers

-- Example 3.1.3
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2; rw [hk]; ring

-- Example 3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨m, hm⟩ := hn
  use 7 * m + 1; rw [hm]; ring

-- Example 3.1.5
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1; rw [ha, hb]; ring

-- Example 3.1.6
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  use 2 * p * q + 3 * q + p + 1; rw [hp, hq]; ring

-- Example 3.1.7
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨k, hk⟩ := hm
  use (3 * k - 1); rw [hk]; ring

-- Example 3.1.8
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨m, hm⟩ := hn
  use 2 * m ^ 2 + 2 * m - 3; rw [hm]; ring

-- Example 3.1.9
example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2; rw [hx]; ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3; rw [hx]; ring

-- Examples 3.1.10
example : Odd (-9 : ℤ) := by
  use -5; numbers

example : Even (26 : ℤ) := by
  use 13; numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  use u + v; rw [hu, hv]; ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  use r - s - 2; rw [hr, hs]; ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 3 * x + y - 1; rw [hx, hy]; ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨u, hu⟩ := hr
  obtain ⟨v, hv⟩ := hs
  use 3 * u - 5 * v - 1; rw [hu, hv]; ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨t, ht⟩ := hx
  use 4 * t ^ 3 + 6 * t ^ 2 + 3 * t; rw [ht]; ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨m, hm⟩ := hn
  use 2 * m ^ 2 - m; rw [hm]; ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨n, hn⟩ := ha
  use 2 * n ^ 2 + 4 * n - 1; rw [hn]; ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨q, hq⟩ := hp
  use 2 * q ^ 2 + 5 * q - 1; rw [hq]; ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  use 2 * s * t + s + t; rw [hs, ht]; ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := by apply Int.even_or_odd n
  . obtain ⟨m, hm⟩ := hn
    use 6 * m ^ 2 + 3 * m - 1; rw [hm]; ring
  . obtain ⟨m, hm⟩ := hn
    use 6 * m ^ 2 + 9 * m + 2; rw [hm]; ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := by apply Int.even_or_odd n
  . use n + 1
    constructor
    . extra
    . obtain ⟨x, hx⟩ := hn
      use x; rw [hx]
  . use n
    constructor
    . extra
    . apply hn

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  . obtain hb | hb := Int.even_or_odd b
    . left
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      use p - q; rw [hp, hq]; ring
    . obtain hc | hc := Int.even_or_odd c
      . right; left
        obtain ⟨p, hp⟩ := ha
        obtain ⟨r, hr⟩ := hc
        use p + r; rw [hp, hr]; ring
      . right; right
        obtain ⟨q, hq⟩ := hb
        obtain ⟨r, hr⟩ := hc
        use q - r; rw [hq, hr]; ring
  . obtain hb | hb := Int.even_or_odd b
    . obtain hc | hc := Int.even_or_odd c
      . right; right
        obtain ⟨q, hq⟩ := hb
        obtain ⟨r, hr⟩ := hc
        use q - r; rw [hq, hr]; ring
      . right; left
        obtain ⟨p, hp⟩ := ha
        obtain ⟨r, hr⟩ := hc
        use p + r + 1; rw [hp, hr]; ring
    . left
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      use p - q; rw [hp, hq]; ring
