-- Prove2me | solution 1 for lean_workbook_plus_30811
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:56:01.832361+00:00
-- url     : https://prove2.me/submissions/6e41c3d8-9be7-4709-8eaf-5df65759e9b2

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.NormNum

private theorem three_residue_certificate : ∀ a b c d : ZMod 3,
    (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) = 0 := by
  decide

private theorem four_residue_certificate : ∀ a b c d : ZMod 4,
    (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) = 0 := by
  decide

theorem integer_difference_divisibility (a b c d : ℤ) :
    12 ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) := by
  have h3 : 3 ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    simpa only [Int.cast_mul, Int.cast_sub] using
      three_residue_certificate (a : ZMod 3) b c d
  have h4 : 4 ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
    simpa only [Int.cast_mul, Int.cast_sub] using
      four_residue_certificate (a : ZMod 4) b c d
  have hc : IsCoprime (3 : ℤ) 4 := ⟨-1, 1, by norm_num⟩
  simpa using hc.mul_dvd h3 h4

theorem common_divisor_classification (k : ℤ) :
    (∀ a b c d : ℤ,
      k ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c)) ↔ k ∣ 12 := by
  constructor
  · intro h
    have hh := h 1 2 3 4
    norm_num at hh
    exact hh
  · intro hk a b c d
    exact hk.trans (integer_difference_divisibility a b c d)

theorem solution (a b c d : ℕ) :
    12 ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) := by
  by_cases hab : a ≤ b
  · simp [Nat.sub_eq_zero_of_le hab]
  by_cases hbc : b ≤ c
  · simp [Nat.sub_eq_zero_of_le hbc]
  by_cases hcd : c ≤ d
  · simp [Nat.sub_eq_zero_of_le hcd]
  have hda : d ≤ a := by omega
  simp [Nat.sub_eq_zero_of_le hda]
