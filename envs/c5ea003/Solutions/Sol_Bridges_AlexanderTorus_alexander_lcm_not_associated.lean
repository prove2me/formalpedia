-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_lcm_not_associated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:11:31.356795+00:00
-- url     : https://prove2.me/submissions/a8e91949-c647-46a8-945a-259218959512

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
open Bridges.AlexanderTorus Polynomial Finset in
theorem solution :
    ¬ Associated (lcm (alexander 3) (alexander 5)) (alexander (Nat.lcm 3 5)) := by
  intro h
  have h15 : Nat.lcm 3 5 = 15 := by norm_num
  rw [h15] at h
  -- explicit forms
  have h3 : alexander 3 = 1 - X + X ^ 2 := by
    simp only [alexander, sum_range_succ, sum_range_zero]
    ring
  have h5 : alexander 5 = 1 - X + X ^ 2 - X ^ 3 + X ^ 4 := by
    simp only [alexander, sum_range_succ, sum_range_zero]
    ring
  have hd15 : (alexander 15).natDegree = 14 := by
    simp only [alexander, sum_range_succ, sum_range_zero]
    compute_degree!
  have hd35 : (alexander 3 * alexander 5).natDegree = 6 := by
    rw [h3, h5]
    compute_degree!
  have hne : alexander 3 * alexander 5 ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd35
    omega
  -- the lcm divides the product, so its degree is at most `6`, but `A₁₅` has degree `14`
  have hle := natDegree_le_of_dvd (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)) hne
  have hdeg := degree_eq_degree_of_associated h
  have hl0 : lcm (alexander 3) (alexander 5) ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hdeg
    have : (alexander 15).natDegree = 0 := by
      rw [natDegree_eq_zero_iff_degree_le_zero, ← hdeg]
      exact bot_le
    omega
  have h15ne : alexander 15 ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd15
    omega
  have := natDegree_eq_of_degree_eq hdeg
  omega
