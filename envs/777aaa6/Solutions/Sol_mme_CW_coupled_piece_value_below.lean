-- Prove2me | solution 1 for mme_CW_coupled_piece_value_below
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T14:53:58.896794+00:00
-- url     : https://prove2.me/submissions/4b50d223-b318-4816-a6ad-f2963a17b1f4

import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_CW_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_coupled_value_cube

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (2 : ℝ) ^ ((2 : ℝ) / 3) *
        (q : ℝ) ^ tau *
        (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) :
    HasSymmetricTauValueAtLeast (coupledObj K q) tau V := by
  have hcube := mme_CW_coupled_value_cube q hq tau
  have hV3 : V ^ (3 : ℕ) <
      4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2) := by
    rw [← hcube]
    exact pow_lt_pow_left₀ hVlt hV (by norm_num)
  exact mme_CW_coupled_raw_cyclic_value_below q hq tau htau
    (V ^ (3 : ℕ)) (by positivity) hV3
