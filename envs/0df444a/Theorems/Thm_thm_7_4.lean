-- Prove2me | Theorems.Thm_thm_7_4
-- name    : thm_7_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:16:57.6652+00:00
-- url     : https://prove2.me/theorems/9d4fcd74-3b45-49c9-b9d4-29ae4d1aef0d
-- title:
--   Chapter 7, thm_7_4: thm_7_4
-- statement:
--   Source theorem `thm_7_4` from Chapter 7, module `thm_7_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_4.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Filter MeasureTheory

theorem thm_7_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
  Integrable X μ ∧
    Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by sorry
