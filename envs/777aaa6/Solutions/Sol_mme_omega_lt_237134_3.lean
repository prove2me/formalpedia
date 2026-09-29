-- Prove2me | solution 3 for mme_omega_lt_237134
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:27:30.730426+00:00
-- url     : https://prove2.me/submissions/29c1d2eb-83a9-489c-a043-209a04b166ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_finite_regional_surplus_certificate
import Theorems.Thm_mme_recursive_regional_CW_plan_omega_bound
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open MME MME.ProfiledCW
universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 237134 / 100000 := by
  obtain ⟨N,ell,P,D,hvolume,hsurplus⟩ := mme_more_asymmetry_finite_regional_surplus_certificate
  have h := mme_recursive_regional_CW_plan_omega_bound (K := K) D
    ((3952233 : ℝ) / 5000000) hvolume hsurplus
  linarith
