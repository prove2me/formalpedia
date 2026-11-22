-- Prove2me | solution 3 for mme_more_asymmetry_entropy_regional_surplus_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-19T20:52:52.966095+00:00
-- url     : https://prove2.me/submissions/1098b04b-e78d-48fd-8e14-c992ed8bce1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_entropy_regional_largeN_surplus_witness
import Theorems.Thm_mme_entropy_regional_smallN_no_surplus
import Theorems.Thm_mme_entropy_regional_smallN_outputs_le_one
import Theorems.Thm_mme_boundary_dims_le_seven_pow
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution : exists (N ell : Nat) (P : Predicate N) (D : EntropyRecipe N ell P), 1 <= D.a * D.b * D.c /\ (((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by
  have hDelimit := mme_entropy_regional_smallN_no_surplus
  have hOut := mme_entropy_regional_smallN_outputs_le_one
  have hDims := mme_boundary_dims_le_seven_pow
  obtain ⟨N, ell, P, D, hN3, hIn1, hDim1, hSur⟩ := mme_entropy_regional_largeN_surplus_witness
  exact ⟨N, ell, P, D, hDim1, hSur⟩
