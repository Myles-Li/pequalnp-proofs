import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  let n := 3 * (E + 1)
  change v < n at hv
  let i := u * n + v
  have hu : u + 1 ≤ n := by omega
  have hi : i < n * n := calc
    i < u * n + n := Nat.add_lt_add_left hv _
    _ = (u + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n hu
  have hs : i + 1 ≤ n * n := hi
  constructor
  · calc
      n + 2 * k * i + p < n + 2 * k * i + 2 * k := Nat.add_lt_add_left hp _
      _ = n + 2 * k * (i + 1) := by ring
      _ ≤ n + 2 * k * (n * n) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
      _ = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by dsimp [n]; ring
  · ring
