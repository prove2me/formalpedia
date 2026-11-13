-- Prove2me | Theorems.Thm_complexTextbookIntegrable_iff_integrable
-- name    : complexTextbookIntegrable_iff_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:32:50.619053+00:00
-- url     : https://prove2.me/theorems/cc4ce896-b1eb-4913-8555-2967892d11c7
-- title:
--   Chapter 6, thm_6_7
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_7`: `complexTextbookIntegrable_iff_integrable`. The mathematical interpretation of this bundle needs review.
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

theorem complexTextbookIntegrable_iff_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  sorry
