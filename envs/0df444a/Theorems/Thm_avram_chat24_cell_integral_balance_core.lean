-- Prove2me | Theorems.Thm_avram_chat24_cell_integral_balance_core
-- name    : avram_chat24_cell_integral_balance_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:48.880604+00:00
-- url     : https://prove2.me/theorems/91733036-445f-406e-8857-325740771062
-- title:
--   avram_chat24_cell_integral_balance_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_cell_integral_balance_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
-- source:
--   candidate-decomposition:ceff8522-80f3-4b18-bd1f-7f8919134883:23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_cell_integral_balance_core
    (ν : Measure (ℝ≥0 × ℝ)) (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (u : ℕ → ℝ≥0) (N : ℕ) (V m e : ℕ → ℝ) (δ h : ℝ) (hh : 0 < h)
    (w : ℝ → ℝ)
    (hmass : ∀ i ∈ Finset.range N,
      let H : ℝ≥0 × ℝ → ℝ := fun p => if u i < p.1 ∧ p.1 ≤ u (i + 1) then -p.2 else 0
      Integrable H ν ∧ (∫ p, H p ∂ν) = m i)
    (hvol : ∀ i ∈ Finset.range N, μ (Ioc (u i) (u (i + 1))) = ENNReal.ofReal h) :
    (∑ i ∈ Finset.range N, e i * (w (V i + δ - m i) - w (V i))) =
      (∫ p, (∑ i ∈ Finset.range N,
        if u i < p.1 ∧ p.1 ≤ u (i + 1) then
          e i * ((w (V i - m i) - w (V i)) / m i) * (-p.2) else 0) ∂ν) +
      (∫ t, (∑ i ∈ Finset.range N,
        if u i < t ∧ t ≤ u (i + 1) then
          e i * ((w (V i + δ - m i) - w (V i - m i)) / h) else 0) ∂μ) := by sorry
end
