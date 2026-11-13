-- Prove2me | Theorems.Thm_thm_7_7_interval
-- name    : thm_7_7_interval
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:00:12.845722+00:00
-- url     : https://prove2.me/theorems/8df6fe4c-c8e1-4794-a7f5-ac190c643dd1
-- title:
--   Chapter 7, thm_7_7: thm_7_7_interval
-- statement:
--   Source theorem `thm_7_7_interval` from Chapter 7, module `thm_7_7`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_7.lean

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

theorem thm_7_7_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Set ℝ) (h0 : ℝ)
    (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hh0 : h0 ∈ I)
    (hXm : ∀ h : ℝ, h ∈ I → AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, h ∈ I → ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h : ℝ => Xh h ω) (nhdsWithin h0 I) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
      (nhds (∫ ω, X ω ∂μ)) := by sorry
