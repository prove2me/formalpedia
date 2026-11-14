-- Prove2me | Theorems.Thm_avram_chat24_uniform_step_integral_public
-- name    : avram_chat24_uniform_step_integral_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:28:06.160703+00:00
-- url     : https://prove2.me/theorems/336eef57-9ca8-4529-ace1-60517098e613
-- title:
--   avram_chat24_uniform_step_integral_public
-- statement:
--   Finite integration of uniform-cell indicators against an integrable coefficient with a prescribed cell antiderivative. This is the exact cellwise sum identity used in avram_chat24_uniform_step_quadrature_core.
-- source:
--   Avram chat24 semantic quadrature decomposition of ee77b723-915c-408a-bf9f-ce2dc9381fe8; source-sha256:4d0f32789604e7ed9472235b401efab4c0a35de3f08b0225a86c677abb9db59c; public counterpart required by parent visibility

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_step_integral_public
    (μ : Measure ℝ≥0) (B : ℝ≥0) (k E C : ℝ≥0 → ℝ)
    (hkI : Integrable k μ)
    (hcell : ∀ s t : ℝ≥0, s ≤ t → t ≤ B →
      (∫ r in Ioc s t, k r ∂μ) = E t - E s) (n : ℕ) :
    let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    (∫ t, (∑ i ∈ Finset.range (n + 1), (Ioc (u i) (u (i + 1))).indicator
      (fun r => k r * C (u i))) t ∂μ) =
      ∑ i ∈ Finset.range (n + 1), (E (u (i + 1)) - E (u i)) * C (u i) := by sorry
end
