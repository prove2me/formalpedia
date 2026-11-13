-- Prove2me | Theorems.Thm_thm_6_7
-- name    : thm_6_7
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:32:35.113965+00:00
-- url     : https://prove2.me/theorems/7eef6677-0477-484d-b627-bcdcb860ec2c
-- title:
--   Chapter 6, thm_6_7: thm_6_7
-- statement:
--   Source theorem `thm_6_7` from Chapter 6, module `thm_6_7`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_7.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Thm67Support

end Thm67Support

theorem thm_6_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegrable μ (fun ω => X ω + Y ω) ∧
      textbookIntegral μ (fun ω => X ω + Y ω) =
        Option.map₂ (fun x y => x + y) (textbookIntegral μ X) (textbookIntegral μ Y) ∧
      textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) ∧
      textbookIntegral μ (fun ω => ((α : EReal) * X ω)) =
        Option.map (fun x => (α : EReal) * x) (textbookIntegral μ X) := by sorry
