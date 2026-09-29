-- Prove2me | Theorems.Thm_LayerCake_expectation_add_const
-- name    : LayerCake.expectation_add_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T00:25:16.779617+00:00
-- url     : https://prove2.me/theorems/cdbd6e48-2938-4f3f-80e1-38b172b786a6
-- title:
--   Expectation via layer-cake
-- statement:
--   Expectation of a shifted bounded variable as an integral of tail probabilities.
--
--   If $W$ is measurable with $|W|\le M$ everywhere, then $E[W+M]=\int_{-M}^M P(W>t)\,dt$ by pointwise layer-cake and Fubini.
--
--   **Formalization Note** Set integrals against `volume`; tail probabilities as `toReal`.
-- source:
--   Layer-cake + Fubini; cf. Mathlib Layercake.lean

import Theorems.Thm_LayerCake_bounded_layercake_identity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem LayerCake.expectation_add_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (hWm : Measurable W) (M : ℝ) (hWb : ∀ ω, |W ω| ≤ M) : ∫ ω, (W ω + M) ∂P = ∫ t in Set.Icc (-M) M, (P {ω | W ω > t}).toReal := by sorry
