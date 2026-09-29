-- Prove2me | solution 1 for mme_stothers_phi233_below_two_thirds_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:28:05.735417+00:00
-- url     : https://prove2.me/submissions/5a2417ff-3995-4a04-8e07-39ce4de8e879

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_scalar_value_below

open MME MME.StothersFourth
universe u
set_option autoImplicit false

/-- Below two thirds, the analytic endpoint is bounded by its value at two thirds. -/
theorem phi233_classValue_le_two_thirds (tau : ℝ) (htau : 3 * tau ≤ 2) :
    classValue 6 tau 9 ≤ 192741120 := by
  let x : ℝ := (6 : ℝ) ^ (3 * tau)
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hx36 : x ≤ 36 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) htau
    norm_num at h
    exact h
  have hE : E 6 tau ≤ 144 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12) htau
    norm_num at h
    exact h
  have hE0 : 0 < E 6 tau := by unfold E; positivity
  have hL : L 6 tau = 4 * x * (x + 2) := rfl
  have hL0 : 0 < L 6 tau := by rw [hL]; positivity
  have hLbound : L 6 tau ≤ 5472 := by rw [hL]; nlinarith
  have h36 : (36 : ℝ) ^ (3 * tau) = x ^ 2 := by
    dsimp [x]
    rw [show (36 : ℝ) = 6 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6),
      mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 6)]
  have hratio := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 38 / 36) htau
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 38)
    (by norm_num : (0 : ℝ) ≤ 36), h36] at hratio
  norm_num at hratio
  have hH : H 6 tau ≤ (1444 / 5472 : ℝ) * L 6 tau := by
    have hh : H 6 tau = (38 : ℝ) ^ (3 * tau) := by norm_num [H]
    have hhbound := (div_le_iff₀ (sq_pos_of_pos hx)).mp hratio
    rw [hh, hL]
    nlinarith [mul_le_mul_of_nonneg_left hx36 hx.le]
  have hsum : (E 6 tau + L 6 tau) ^ 2 ≤ (5616 : ℝ) ^ 2 := by nlinarith
  change 4 * (E 6 tau + L 6 tau) ^ 2 *
    (2 * H 6 tau + L 6 tau) / L 6 tau ≤ 192741120
  apply (div_le_iff₀ hL0).2
  have hfactor : 2 * H 6 tau + L 6 tau ≤ (1045 / 684 : ℝ) * L 6 tau := by
    linarith
  have hprod := mul_le_mul_of_nonneg_left hfactor
    (by positivity : 0 ≤ 4 * (E 6 tau + L 6 tau) ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right hsum hL0.le]


/-- The full analytic bound holds throughout the range below two thirds. -/
theorem solution
    {K : Type u} [Field K] (tau V : ℝ) (htau : 3 * tau ≤ 2)
    (hV : 0 ≤ V) (hVlt : V < classValue 6 tau 9) :
    HasTauValueAtLeast (cyclicSymmetrization
      (cwFourthConstituent K 6 2 3 3)) tau V := by
  exact mme_stothers_phi233_scalar_value_below tau V hV
    (hVlt.trans_le (phi233_classValue_le_two_thirds tau htau))

