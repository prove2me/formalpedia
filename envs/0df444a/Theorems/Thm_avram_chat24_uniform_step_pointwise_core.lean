-- Prove2me | Theorems.Thm_avram_chat24_uniform_step_pointwise_core
-- name    : avram_chat24_uniform_step_pointwise_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:48:03.284206+00:00
-- url     : https://prove2.me/theorems/8cf5a0d3-4f34-4b23-b6d6-1e9901c264a6
-- title:
--   avram_chat24_uniform_step_pointwise_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_uniform_step_pointwise_core from oversized parent candidate 0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527.
-- source:
--   candidate-decomposition:966a885e-1f3b-4988-ade7-7c1ab4049f80:0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_step_pointwise_core
    (F Y : ℝ≥0 → ℝ) (a b : ℝ) (B : ℝ≥0) (hB : 0 < B)
    (hband : ∀ s, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b))
    (k : ℝ≥0 → ℝ) (L M : ℝ) (hL : 0 ≤ L)
    (hkb : ∀ t, ‖k t‖ ≤ L) (hM : ∀ y ∈ Icc a b, ‖w y‖ ≤ M) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let G : ℕ → ℝ≥0 → ℝ := fun n =>
      ∑ i ∈ Finset.range (n + 1), (Ioc (u n i) (u n (i + 1))).indicator
        (fun t => k t * w (F (u n i)))
    ∀ t : ℝ≥0, 0 < t → t ≤ B →
      (∀ n, ‖G n t‖ ≤ L * M) ∧
      Tendsto (fun n => G n t) atTop (nhds (k t * w (Y t))) := by sorry
end
