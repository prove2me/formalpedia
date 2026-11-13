-- Prove2me | Theorems.Thm_thm_7_7_sequential_complex_DCT
-- name    : thm_7_7_sequential_complex_DCT
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:00:01.366206+00:00
-- url     : https://prove2.me/theorems/9910993a-ee28-41b7-86bb-0c2c6e518cf2
-- title:
--   Chapter 7, thm_7_7: thm_7_7_sequential_complex_DCT
-- statement:
--   Source theorem `thm_7_7_sequential_complex_DCT` from Chapter 7, module `thm_7_7`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_7.lean

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

theorem thm_7_7_sequential_complex_DCT {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) := by sorry
