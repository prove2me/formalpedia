-- Prove2me | Theorems.Thm_avram_chat24_uniform_step_quadrature_core
-- name    : avram_chat24_uniform_step_quadrature_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:48:07.082202+00:00
-- url     : https://prove2.me/theorems/ee77b723-915c-408a-bf9f-ce2dc9381fe8
-- title:
--   avram_chat24_uniform_step_quadrature_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_uniform_step_quadrature_core from oversized parent candidate 0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527.
-- source:
--   candidate-decomposition:966a885e-1f3b-4988-ade7-7c1ab4049f80:0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_step_quadrature_core
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (hzero : μ {0} = 0)
    (F Y : ℝ≥0 → ℝ) (a b : ℝ) (B : ℝ≥0) (hB : 0 < B)
    (hband : ∀ s, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b))
    (k E : ℝ≥0 → ℝ) (hk : Measurable k)
    (L : ℝ) (hL : 0 ≤ L) (hkb : ∀ t, ‖k t‖ ≤ L)
    (hcell : ∀ s t : ℝ≥0, s ≤ t → t ≤ B →
      (∫ r in Ioc s t, k r ∂μ) = E t - E s) :
    let A : ℝ≥0 → ℝ := fun t =>
      if t ≤ B ∧ Y t ∈ Icc a b then k t * w (Y t) else 0
    Integrable A μ ∧ Tendsto (fun n : ℕ =>
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
      ∑ i ∈ Finset.range (n + 1), (E (u (i + 1)) - E (u i)) * w (F (u i)))
      atTop (nhds (∫ t, A t ∂μ)) := by sorry
end
