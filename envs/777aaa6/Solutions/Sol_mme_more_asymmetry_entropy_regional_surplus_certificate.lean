-- Prove2me | solution 1 for mme_more_asymmetry_entropy_regional_surplus_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T07:28:44.147176+00:00
-- url     : https://prove2.me/submissions/5ce52233-2121-40e8-ba96-0e8462e992a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_entropy_regional_witness
import Theorems.Thm_mme_entropy_surplus_arith
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution :
    ∃ (N ell : ℕ) (P : Predicate N) (D : EntropyRecipe N ell P),
      1 ≤ D.a * D.b * D.c ∧
      ((D.inputs * 7 ^ N : ℕ) : ℝ) <
        (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
  obtain ⟨ell, P, D, h_in, h_out, h_dims, h_pos⟩ := mme_entropy_regional_witness
  refine ⟨2, ell, P, D, h_pos, ?_⟩
  have h49 : D.inputs * 7 ^ 2 = 49 := by
    rw [h_in]
    decide
  rw [h49, h_out, h_dims]
  exact mme_entropy_surplus_arith
