-- Prove2me | solution 1 for lean_workbook_plus_75865
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:36:13.581813+00:00
-- url     : https://prove2.me/submissions/439668ad-4479-4379-8358-44419aa0445f

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace TwoSevenPowers

theorem seven_residue (y : ℕ) : 7 ^ y % 16 = 1 ∨ 7 ^ y % 16 = 7 := by
  induction y with
  | zero => norm_num
  | succ y ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> norm_num [h]

theorem exponent_bound (x y : ℕ) (h : 2 ^ x - 1 = 7 ^ y) : x < 4 := by
  have hp : 0 < 2 ^ x := pow_pos (by decide) _
  have he : 2 ^ x = 7 ^ y + 1 := by omega
  by_contra hx
  have hd : 16 ∣ 2 ^ x := by
    have := pow_dvd_pow 2 (show 4 ≤ x by omega)
    exact this
  have hz : 2 ^ x % 16 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hm := congrArg (fun n : ℕ => n % 16) he
  rcases seven_residue y with h7 | h7 <;> norm_num [Nat.add_mod, hz, h7] at hm

theorem classification (x y : ℕ) :
    2 ^ x - 1 = 7 ^ y ↔ (x = 1 ∧ y = 0) ∨ (x = 3 ∧ y = 1) := by
  constructor
  · intro h
    have hx := exponent_bound x y h
    interval_cases x
    · have hp : 0 < 7 ^ y := pow_pos (by decide) _
      norm_num at h
      omega
    · left
      refine ⟨rfl, Nat.pow_right_injective (by decide : 2 ≤ 7) ?_⟩
      simpa using h.symm
    · have hy : 0 < y := by
        by_contra hy
        have : y = 0 := by omega
        simp [this] at h
      have hb : 7 ^ 1 ≤ 7 ^ y := Nat.pow_le_pow_right (by decide) hy
      norm_num at h hb
      omega
    · right
      refine ⟨rfl, Nat.pow_right_injective (by decide : 2 ≤ 7) ?_⟩
      simpa using h.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem full_solution_set :
    {(x, y) : ℕ × ℕ | 2 ^ x - 1 = 7 ^ y} = {(1, 0), (3, 1)} := by
  ext ⟨x, y⟩
  simp [classification, Prod.mk.injEq]

theorem positive_classification (x y : ℕ) (hy : 0 < y) :
    2 ^ x - 1 = 7 ^ y ↔ x = 3 ∧ y = 1 := by
  rw [classification]
  omega

end TwoSevenPowers

theorem solution :
    ¬ ({(x, y) : ℕ × ℕ | 2 ^ x - 1 = 7 ^ y} = {(3, 1)}) := by
  intro h
  have hm : (1, 0) ∈ {(x, y) : ℕ × ℕ | 2 ^ x - 1 = 7 ^ y} := by norm_num
  rw [h] at hm
  norm_num at hm
