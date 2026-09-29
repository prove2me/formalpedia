-- Prove2me | solution 1 for BonferroniMarginals.chung_erdos_dominates_bonferroni
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:44:31.795986+00:00
-- url     : https://prove2.me/submissions/397d9d02-a6de-469f-82c9-251de43861f5

import Mathlib
import Definitions.Def_Geometry_BonferroniMarginals
open BonferroniMarginals in
theorem solution {k M : ℕ} (hM : 0 < M) (hk : k ≤ M + 1) :
    (k : ℝ) / (2 * M) ≤ (k : ℝ) / ((M : ℝ) + k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · -- same numerator, and `0 < M + k - 1 ≤ 2M`
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkM : (k : ℝ) ≤ M + 1 := by exact_mod_cast hk
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
