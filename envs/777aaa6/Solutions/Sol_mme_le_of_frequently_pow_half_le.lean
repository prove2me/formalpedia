-- Prove2me | solution 1 for mme_le_of_frequently_pow_half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:20:26.960266+00:00
-- url     : https://prove2.me/submissions/4b9e344e-78bb-4b93-b2ca-290538b5d017

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-!
An elementary analytic endpoint used by the tau-value/rank bridge.  A
frequently occurring exponential inequality with a fixed positive loss still
forces the base on the left to be no larger than the base on the right.
-/

theorem solution {V R : ℝ}
    (hV : 1 ≤ V) (hR : 0 ≤ R)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      V ^ N * (1 / 2 : ℝ) ≤ R ^ N) :
    V ≤ R := by
  by_contra hnot
  have hVR : R < V := lt_of_not_ge hnot
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hratio_nonneg : 0 ≤ R / V := div_nonneg hR hVpos.le
  have hratio_lt_one : R / V < 1 := (div_lt_one hVpos).2 hVR
  have htend : Tendsto (fun N : ℕ => (R / V) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt_one
  have hevent : ∀ᶠ N : ℕ in atTop, (R / V) ^ N < (1 / 2 : ℝ) :=
    (tendsto_order.1 htend).2 _ (by norm_num)
  rcases (hfreq.and_eventually hevent).exists with ⟨N, hpow, hsmall⟩
  have hVpow : 0 < V ^ N := pow_pos hVpos N
  have hhalf : (1 / 2 : ℝ) ≤ R ^ N / V ^ N := by
    apply (le_div_iff₀ hVpow).2
    simpa [mul_comm] using hpow
  rw [← div_pow] at hhalf
  exact (not_lt_of_ge hhalf) hsmall
