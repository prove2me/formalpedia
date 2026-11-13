-- Prove2me | Theorems.Thm_complexTextbookIntegral_eq_none_of_not_integrable
-- name    : complexTextbookIntegral_eq_none_of_not_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:29:40.426966+00:00
-- url     : https://prove2.me/theorems/a30a9e91-5d67-42c4-91aa-3311519a9a14
-- title:
--   ProbabilityTheory_chapter_06_def_6_6_F000: complexTextbookIntegral_eq_none_of_not_integrable
-- statement:
--   Source theorem `complexTextbookIntegral_eq_none_of_not_integrable` extracted from `ProbabilityTheory.chapter_06.def_6_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_6.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
namespace Def66RealSupport
end Def66RealSupport

theorem complexTextbookIntegral_eq_none_of_not_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : ¬ complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = none := by
  sorry
