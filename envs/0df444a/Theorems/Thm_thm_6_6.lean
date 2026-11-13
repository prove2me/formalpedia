-- Prove2me | Theorems.Thm_thm_6_6
-- name    : thm_6_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:16:15.954393+00:00
-- url     : https://prove2.me/theorems/ea3931d1-9edc-45f4-aa7e-f89714c6bd03
-- title:
--   ProbabilityTheory_chapter_06_thm_6_6_F000: thm_6_6
-- statement:
--   Source theorem `thm_6_6` extracted from `ProbabilityTheory.chapter_06.thm_6_6`. The formal Lean declaration specifies the proposition.
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

theorem thm_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal)
    (_hXm : Measurable X) :
    ((∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤ ∧
        (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤) ↔
      (∫⁻ ω, (X ω).toENNReal ∂μ) + (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤ := by
  sorry
