-- Prove2me | solution 1 for mme_CW_coupled_raw_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T14:53:10.999441+00:00
-- url     : https://prove2.me/submissions/9304948b-633d-42e0-ba83-163e1f4b3774

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_CW_coupled_tensor_extraction_below_raw
import Theorems.Thm_mme_CW_coupled_floor_pruning
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (q : ℝ) ^ (3 * tau) *
        ((q : ℝ) ^ (3 * tau) + 2)) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K q)) tau V := by
  have hround := mme_CW_coupled_floor_pruning q hq tau htau
  have hcore :=
    mme_CW_coupled_tensor_extraction_below_raw (K := K) q hq tau htau V hV hVlt
  have hs : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (cyclicSymmetrization (coupledObj K q)) tau V hV
    (fun N => 2 * N) hs (fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hround, hcore] with N hround hcore
  dsimp only at hround hcore
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hcore hround
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simpa only [sub_zero, mul_one] using hweight
