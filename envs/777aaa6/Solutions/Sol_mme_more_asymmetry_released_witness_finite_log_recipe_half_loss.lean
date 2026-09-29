-- Prove2me | solution 1 for mme_more_asymmetry_released_witness_finite_log_recipe_half_loss
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-23T19:38:50.410415+00:00
-- url     : https://prove2.me/submissions/7907c059-edc4-4d37-9b7e-fe0a6e4585ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Theorems.Thm_mme_more_asymmetry_cofinal_explicit_child_witness
import Theorems.Thm_mme_more_asymmetry_finite_log_recipe_half_loss_from_cofinal_explicit_child_witness

open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution :
    ∃ (n ell : ℕ) (P : Predicate (4 * n)) (D : LogRecipe (4 * n) ell P),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 2000000) +
          Real.log (D.inputs : ℝ) ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 20000000) ≤
          Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
  exact mme_more_asymmetry_finite_log_recipe_half_loss_from_cofinal_explicit_child_witness
    (K := ℝ)
    (mme_more_asymmetry_cofinal_explicit_child_witness (K := ℝ))
