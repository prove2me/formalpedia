-- Prove2me | solution 1 for mme_CW_q6_coupled_raw_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:13:54.8145+00:00
-- url     : https://prove2.me/submissions/d39a81b5-1d69-42b6-ad56-2ab7e13124d6

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_CW_q6_coupled_even_power_finite_extractions_below_raw
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V := by
  have hextract :=
    mme_CW_q6_coupled_even_power_finite_extractions_below_raw
      (K := K) tau htau V hV hVlt
  have hs : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (cyclicSymmetrization (coupledObj K 6)) tau V hV
    (fun N => 2 * N) hs (fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hextract] with N hN
  dsimp only at hN
  obtain ⟨_hL, _hsum, _hratio, k, a, b, c, hrestrict, hweight⟩ := hN
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simpa only [sub_zero, mul_one] using hweight
