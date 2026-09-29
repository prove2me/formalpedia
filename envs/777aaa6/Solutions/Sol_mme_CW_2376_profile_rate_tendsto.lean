-- Prove2me | solution 1 for mme_CW_2376_profile_rate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:56:53.793685+00:00
-- url     : https://prove2.me/submissions/f641f7c0-ba7f-46a9-9055-64139b14a2b2

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_2376_profile_data

open MME Filter

theorem solution :
    Tendsto cw2376ProfileRate atTop (nhds 0) ∧
      ∀ m : ℕ, 0 ≤ cw2376ProfileRate m := by
  have hbase :
      Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsqrt :
      Tendsto
        (fun m : ℕ => Real.sqrt (Real.sqrt ((m : ℝ) + 1)))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hbase)
  constructor
  · simpa [cw2376ProfileRate] using hsqrt.inv_tendsto_atTop
  · intro m
    unfold cw2376ProfileRate
    positivity
