-- Prove2me | Theorems.Thm_continuous_preimage_borel
-- name    : continuous_preimage_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:57:38.536679+00:00
-- url     : https://prove2.me/theorems/e7036b09-bdd9-400a-b984-f00e2b050aac
-- title:
--   04_thm_4_5: continuous_preimage_borel
-- statement:
--   Original source theorem `continuous_preimage_borel` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_5.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
section Theorem_4_5
open MeasureTheory

theorem continuous_preimage_borel {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B) := by
  sorry
end Theorem_4_5
