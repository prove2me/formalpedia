-- Prove2me | solution 1 for mme_more_asymmetry_released_witness_joint_log_recipe
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:19:10.240551+00:00
-- url     : https://prove2.me/submissions/c7f15024-2301-4e54-811e-b7b1e3f9cf92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_released_witness_finite_log_recipe
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe

open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution :
    ∃ (n ell : ℕ) (P : Predicate (4 * n)) (D : LogJointRecipe (4 * n) ell P),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
          Real.log (D.inputs : ℝ) ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
          Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
  obtain ⟨n, ell, P, D, hn, hinputs, hvolume, houtputs, hdims⟩ :=
    mme_more_asymmetry_released_witness_finite_log_recipe
  refine ⟨n, ell, P, LogJointRecipe.base D, hn, hinputs, hvolume, ?_, ?_⟩
  · exact houtputs
  · exact hdims
