-- Prove2me | Theorems.Thm_continuous_to_borel_measurable
-- name    : continuous_to_borel_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:57:29.720062+00:00
-- url     : https://prove2.me/theorems/8faf6d7b-994d-46c9-8abf-ccb5b67d88c0
-- title:
--   04_thm_4_5: continuous_to_borel_measurable
-- statement:
--   Original source theorem `continuous_to_borel_measurable` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_5.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
section Theorem_4_5
open MeasureTheory

theorem continuous_to_borel_measurable {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) : Measurable f := by
  sorry
end Theorem_4_5
