-- Prove2me | Theorems.Thm_avram_chat24_uniform_step_DCT_public
-- name    : avram_chat24_uniform_step_DCT_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:28:07.658367+00:00
-- url     : https://prove2.me/theorems/271947b7-2b35-4599-a03c-d090c868ef75
-- title:
--   avram_chat24_uniform_step_DCT_public
-- statement:
--   Dominated convergence for strict-left uniform-cell step functions on a finite nonnegative-real measure, using bounded coefficients and prescribed left limits. This isolates the limit and integrability step in avram_chat24_uniform_step_quadrature_core.
-- source:
--   Avram chat24 semantic quadrature decomposition of ee77b723-915c-408a-bf9f-ce2dc9381fe8; source-sha256:4d0f32789604e7ed9472235b401efab4c0a35de3f08b0225a86c677abb9db59c; public counterpart required by parent visibility

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_step_DCT_public
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (hzero : μ {0} = 0)
    (F Y : ℝ≥0 → ℝ) (a b : ℝ) (B : ℝ≥0) (hB : 0 < B)
    (hband : ∀ s, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b))
    (k : ℝ≥0 → ℝ) (hk : Measurable k)
    (L : ℝ) (hL : 0 ≤ L) (hkb : ∀ t, ‖k t‖ ≤ L) :
    let A : ℝ≥0 → ℝ := fun t =>
      if t ≤ B ∧ Y t ∈ Icc a b then k t * w (Y t) else 0
    Integrable A μ ∧ Tendsto (fun n : ℕ =>
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
      ∫ t, (∑ i ∈ Finset.range (n + 1), (Ioc (u i) (u (i + 1))).indicator
        (fun r => k r * w (F (u i)))) t ∂μ)
      atTop (nhds (∫ t, A t ∂μ)) := by sorry
end
