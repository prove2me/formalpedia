-- Prove2me | solution 1 for mme_dwz_q5_boundary_original_profile_log_floors
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:55:09.682488+00:00
-- url     : https://prove2.me/submissions/8f06e135-7396-4b9b-8d66-ddcb5d9e51dd

import Definitions.Def_mme_CW_q5_fourth_boundary_alphabet_data
import Definitions.Def_mme_dwz_q5_global_component_ledger_data
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
import Mathlib.Tactic
open MME MME.CWFourthBoundaryQ5 MME.DWZQ5GlobalLedger MME.DWZQ5ExactData
open MME.DWZFourthGlobalWitness MME.DWZRestrictedValue
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

private def shift : Fin 9 → Fin 5 → ℕ :=
  ![![0,0,0,0,0], ![5,5,0,0,0], ![8,8,8,0,0],
    ![9,10,10,9,0], ![9,10,10,10,9], ![0,9,10,10,9],
    ![0,0,8,8,8], ![0,0,0,5,5], ![0,0,0,0,0]]
private def frequency (p : IntegerZSplitProfile 5) (a : Fin 5) : ℚ :=
  (p.count a : ℚ) / p.denominator
private def ratio (k : Fin 9) (p : IntegerZSplitProfile 5) (a : Fin 5) : ℚ :=
  frequency p a / positiveSize k a
private def termFloor (k : Fin 9) (p : IntegerZSplitProfile 5) (a : Fin 5) : ℚ :=
  if p.count a = 0 then 0 else
    - frequency p a * autoScaledLogUpper (ratio k p a) (shift k a) 8

private theorem termFloor_le (k : Fin 9) (p : IntegerZSplitProfile 5) (a : Fin 5)
    (hscale : p.count a ≠ 0 → 1 ≤ ratio k p a * 2 ^ shift k a) :
    (termFloor k p a : ℝ) ≤
      Real.negMulLog ((p.count a : ℝ) / p.denominator) +
        ((p.count a : ℝ) / p.denominator) * Real.log (positiveSize k a) := by
  by_cases hz : p.count a = 0
  · simp [termFloor, hz, Real.negMulLog]
  have hd : 0 < positiveSize k a := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hpQ : 0 < frequency p a := by
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hz)
      (by exact_mod_cast p.denominator_pos)
  have hq : 0 < ratio k p a := div_pos hpQ (by exact_mod_cast hd)
  have hu := (mme_log_interval_of_auto_scaled_rational
    (ratio k p a) (shift k a) 8 hq (hscale hz)).2
  have hp : 0 < (p.count a : ℝ) / p.denominator := by
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hz)
      (by exact_mod_cast p.denominator_pos)
  have hdR : 0 < (positiveSize k a : ℝ) := by exact_mod_cast hd
  have hqR : (ratio k p a : ℝ) =
      ((p.count a : ℝ) / p.denominator) / positiveSize k a := by
    unfold ratio frequency
    push_cast
    rfl
  rw [hqR, Real.log_div hp.ne' hdR.ne'] at hu
  have h := mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr hp.le)
  unfold termFloor
  rw [if_neg hz]
  unfold frequency
  push_cast
  unfold Real.negMulLog
  nlinarith only [h]

private theorem scales_valid (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) (a : Fin 5) :
    (rawProfile c).count a ≠ 0 →
      1 ≤ ratio (coarseAddress c 2) (rawProfile c) a *
        2 ^ shift (coarseAddress c 2) a := by
  revert a hc c
  decide +kernel

private theorem rational_floor (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) :
    componentLogFloor c ≤ (790643 / 1000000 : ℚ) *
      ∑ a, termFloor (coarseAddress c 2) (rawProfile c) a := by
  revert hc c
  decide +kernel

theorem solution (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) :
    (componentLogFloor c : ℝ) ≤
      (790643 / 1000000 : ℝ) * logDimension (coarseAddress c 2) (rawProfile c) := by
  have h := rational_floor c hc
  have hR : (componentLogFloor c : ℝ) ≤
      (790643 / 1000000 : ℝ) *
        ∑ a, (termFloor (coarseAddress c 2) (rawProfile c) a : ℝ) := by
    have h' : (componentLogFloor c : ℝ) ≤
        (((790643 / 1000000 : ℚ) * ∑ a, termFloor (coarseAddress c 2) (rawProfile c) a : ℚ) : ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] using h'
  apply hR.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 790643 / 1000000)
  rw [logDimension, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a _ ↦ termFloor_le _ _ _ (scales_valid c hc a))
