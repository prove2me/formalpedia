-- Prove2me | Theorems.Thm_covariance_zero_iff_uncorrelated
-- name    : covariance_zero_iff_uncorrelated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:07:50.465206+00:00
-- url     : https://prove2.me/theorems/e566f12f-1dd0-4b06-a4b3-e2a29dafec41
-- title:
--   ProbabilityTheory_chapter_07_def_7_3_F000: covariance_zero_iff_uncorrelated
-- statement:
--   Source theorem `covariance_zero_iff_uncorrelated` extracted from `ProbabilityTheory.chapter_07.def_7_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/def_7_3.lean

import Definitions.Def_ProbabilityTheory_chapter_07_def_7_3_F000
import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_13_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory

theorem covariance_zero_iff_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Covariance μ X Y = 0 ↔ Uncorrelated μ X Y := by
  sorry
