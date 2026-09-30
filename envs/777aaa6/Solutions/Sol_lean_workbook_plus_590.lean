-- Prove2me | solution 1 for lean_workbook_plus_590
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:52:07.903382+00:00
-- url     : https://prove2.me/submissions/facf229a-b1c8-4304-b8bf-82a49f07a8d5

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem cubic_sum_parameter_data (x y z k : ℤ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y)
    (hs : x + y = k) (hc : x ^ 3 + y ^ 3 = k * z ^ 3) :
    z ^ 3 = k ^ 2 - 3 * k * x + 3 * x ^ 2 ∧
      (4 * z ^ 3 - k ^ 2) / 3 = (y - x) ^ 2 ∧
      k ^ 2 < 4 * z ^ 3 ∧ z ^ 3 < k ^ 2 := by
  have hk : 0 < k := by omega
  have hfactor : x ^ 3 + y ^ 3 = k * (k ^ 2 - 3 * x * y) := by
    rw [← hs]
    ring
  have hz : z ^ 3 = k ^ 2 - 3 * x * y := by
    apply mul_left_cancel₀ (ne_of_gt hk)
    exact hc.symm.trans hfactor
  have hform : z ^ 3 = k ^ 2 - 3 * k * x + 3 * x ^ 2 := by
    rw [hz, ← hs]
    ring
  have hsquare : 4 * z ^ 3 - k ^ 2 = 3 * (y - x) ^ 2 := by
    rw [hz, ← hs]
    ring
  refine ⟨hform, ?_, ?_, ?_⟩
  · omega
  · have hpos : 0 < (y - x) ^ 2 := sq_pos_of_pos (by omega)
    omega
  · have hpos : 0 < x * y := mul_pos hx hy
    nlinarith

theorem cubic_sum_parameter_twenty_classification (x y z : ℤ) :
    (0 < x ∧ 0 < y ∧ 0 < z ∧ x < y ∧ x + y = 20 ∧
      x ^ 3 + y ^ 3 = 20 * z ^ 3) ↔ x = 1 ∧ y = 19 ∧ z = 7 := by
  constructor
  · rintro ⟨hx, hy, hz, hxy, hs, hc⟩
    obtain ⟨he, _, hlo, hhi⟩ := cubic_sum_parameter_data x y z 20 hx hy hxy hs hc
    have hx1 : 1 ≤ x := by omega
    have hx9 : x ≤ 9 := by omega
    have hz5 : 5 ≤ z := by
      by_contra h
      have hb : z ≤ 4 := by omega
      have hp := pow_le_pow_left₀ (show 0 ≤ z by omega) hb 3
      norm_num at hp hlo
      omega
    have hz7 : z ≤ 7 := by
      by_contra h
      have hb : 8 ≤ z := by omega
      have hp := pow_le_pow_left₀ (show (0 : ℤ) ≤ 8 by decide) hb 3
      norm_num at hp hhi
      omega
    interval_cases x <;> interval_cases z <;> norm_num at he
    all_goals omega
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem solution (x y z k : ℤ) (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
    (h₂ : x < y) (h₃ : x + y = k) (h₄ : x ^ 3 + y ^ 3 = k * z ^ 3) :
    z ^ 3 = k ^ 2 - 3 * k * x + 3 * x ^ 2 := by
  exact (cubic_sum_parameter_data x y z k h₁.1 h₁.2.1 h₂ h₃ h₄).1
