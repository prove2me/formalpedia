-- Prove2me | Theorems.Thm_thm_7_6
-- name    : thm_7_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:44:09.61088+00:00
-- url     : https://prove2.me/theorems/1b6b115b-cb88-4e64-ae26-3aebc65d1585
-- title:
--   Chapter 7, thm_7_6: thm_7_6
-- statement:
--   Source theorem `thm_7_6` from Chapter 7, module `thm_7_6`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_6.lean

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory

theorem thm_7_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by sorry
