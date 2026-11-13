-- Prove2me | Theorems.Thm_avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
-- name    : avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:20:38.978477+00:00
-- url     : https://prove2.me/theorems/48a80582-d8f3-46c3-92a4-d4a0bfcceeb1
-- title:
--   Finite linear Gaussian local-time upper bound tends to zero as band narrows
-- statement:
--   The real widths 1/(k+1) shrink to zero, so each finite linear local-time upper bound ENNReal.ofReal(L/(k+1)) also tends to zero; combined with B168 gives an explicit quantitative-to-qualitative Gaussian occupation transfer.

import Mathlib
open Filter Topology
open scoped ENNReal NNReal
noncomputable section

theorem avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero (L : ℝ≥0) :
    Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
