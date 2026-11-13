-- Prove2me | Theorems.Thm_thm_6_7_complex
-- name    : thm_6_7_complex
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:33:02.237213+00:00
-- url     : https://prove2.me/theorems/e45991f9-5025-4691-93db-1b1e68ad6b0b
-- title:
--   Chapter 6, thm_6_7: thm_6_7_complex
-- statement:
--   Source theorem `thm_6_7_complex` from Chapter 6, module `thm_6_7`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_7.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Thm67Support

end Thm67Support

theorem thm_6_7_complex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by sorry
