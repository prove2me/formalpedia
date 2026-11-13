-- Prove2me | Theorems.Thm_thm_6_6_complex
-- name    : thm_6_6_complex
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:16:38.808201+00:00
-- url     : https://prove2.me/theorems/14960a94-4f1a-4d6c-a60d-b8abef56caa5
-- title:
--   ProbabilityTheory_chapter_06_thm_6_6_F000: thm_6_6_complex
-- statement:
--   Source theorem `thm_6_6_complex` extracted from `ProbabilityTheory.chapter_06.thm_6_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_6.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
namespace Thm66Support
open Def66RealSupport
end Thm66Support

theorem thm_6_6_complex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (hZm : Measurable Z) :
    ((∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ) < ⊤ ∧
        (∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ) < ⊤) ↔
      (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ) < ⊤ := by
  sorry
