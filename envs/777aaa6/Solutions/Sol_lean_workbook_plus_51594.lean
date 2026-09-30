-- Prove2me | solution 1 for lean_workbook_plus_51594
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:43:53.856651+00:00
-- url     : https://prove2.me/submissions/a16b04c7-ec31-4005-b190-27f7347a78c2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

theorem separated_octic_sextic_gap (a b : ℝ) :
    2 * a ^ 8 + 2 * b ^ 6 + a ^ 4 - b ^ 3 - 2 * a ^ 2 - 2 + 11 / 4 =
      (a ^ 2 - 1 / 2) ^ 2 * (2 * a ^ 4 + 2 * a ^ 2 + 5 / 2) +
        2 * (b ^ 3 - 1 / 4) ^ 2 := by ring

theorem solution (a b : ℝ) :
    (2 * a ^ 8 + 2 * b ^ 6 + a ^ 4 - b ^ 3 - 2 * a ^ 2 - 2 : ℝ) ≥ -11 / 4 := by
  have ha : 0 ≤ (a ^ 2 - 1 / 2) ^ 2 * (2 * a ^ 4 + 2 * a ^ 2 + 5 / 2) := by positivity
  nlinarith [separated_octic_sextic_gap a b, sq_nonneg (b ^ 3 - 1 / 4)]

theorem separated_octic_sextic_equality (a b : ℝ) :
    2 * a ^ 8 + 2 * b ^ 6 + a ^ 4 - b ^ 3 - 2 * a ^ 2 - 2 = -11 / 4 ↔
      a ^ 2 = 1 / 2 ∧ b ^ 3 = 1 / 4 := by
  have hi := separated_octic_sextic_gap a b
  constructor
  · intro he
    have hc : 0 < 2 * a ^ 4 + 2 * a ^ 2 + 5 / 2 := by positivity
    have ha : 0 ≤ (a ^ 2 - 1 / 2) ^ 2 * (2 * a ^ 4 + 2 * a ^ 2 + 5 / 2) := by positivity
    have hb := sq_nonneg (b ^ 3 - 1 / 4)
    have hprod : (a ^ 2 - 1 / 2) ^ 2 * (2 * a ^ 4 + 2 * a ^ 2 + 5 / 2) = 0 := by nlinarith
    have hbsq : (b ^ 3 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hasq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hc)
    exact ⟨by linarith [sq_eq_zero_iff.mp hasq], by linarith [sq_eq_zero_iff.mp hbsq]⟩
  · rintro ⟨ha, hb⟩
    have hz : (a ^ 2 - 1 / 2) ^ 2 * (2 * a ^ 4 + 2 * a ^ 2 + 5 / 2) +
        2 * (b ^ 3 - 1 / 4) ^ 2 = 0 := by simp [ha, hb]
    rw [hz] at hi
    linarith

theorem quarter_unique_real_cube_root : ∃! b : ℝ, b ^ 3 = 1 / 4 := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ 3) (Set.Icc 0 1) :=
    (continuous_id.pow 3).continuousOn
  obtain ⟨b, hbinterval, hb⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont
    (show (1 / 4 : ℝ) ∈ Set.Icc ((0 : ℝ) ^ 3) ((1 : ℝ) ^ 3) by norm_num)
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact (by decide : Odd 3).pow_inj.mp (hc.trans hb.symm)

theorem separated_octic_sextic_attainment :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      2 * a ^ 8 + 2 * b ^ 6 + a ^ 4 - b ^ 3 - 2 * a ^ 2 - 2 = -11 / 4 := by
  obtain ⟨b, hb, _⟩ := quarter_unique_real_cube_root
  have hbpos : 0 < b := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) (le_of_not_gt h)
    nlinarith
  refine ⟨Real.sqrt (1 / 2), b, Real.sqrt_pos.2 (by norm_num), hbpos, ?_⟩
  exact (separated_octic_sextic_equality _ _).2 ⟨Real.sq_sqrt (by norm_num), hb⟩

#print axioms solution
#print axioms separated_octic_sextic_gap
#print axioms separated_octic_sextic_equality
#print axioms quarter_unique_real_cube_root
#print axioms separated_octic_sextic_attainment
