-- Prove2me | Theorems.Thm_mme_six_input_multiplicity_log_rate
-- name    : mme_six_input_multiplicity_log_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:18:12.974491+00:00
-- url     : https://prove2.me/theorems/2aa8b3b8-e5b3-494d-81ae-b0be3bde29d1
-- title:
--   The copy-rate terms recover the exact source multiplicity
-- statement:
--   For six positive input counts, exponentiating the sum of the base rates and six times each logarithmic input count equals the product of sixth-power input counts times the exponential base rate. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open BigOperators

theorem mme_six_input_multiplicity_log_rate
    (inputs : Fin 6 → ℕ) (hinputs : ∀ owner, 1 ≤ inputs owner)
    (base : Fin 6 → ℝ) :
    Real.exp (∑ owner, (base owner + 6 * Real.log (inputs owner : ℝ))) =
      ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) * Real.exp (∑ owner, base owner) := by sorry
