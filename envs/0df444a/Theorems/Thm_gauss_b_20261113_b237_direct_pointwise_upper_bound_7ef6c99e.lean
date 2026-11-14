-- Prove2me | Theorems.Thm_gauss_b_20261113_b237_direct_pointwise_upper_bound_7ef6c99e
-- name    : gauss_b_20261113_b237_direct_pointwise_upper_bound_7ef6c99e
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T11:20:25.962208+00:00
-- url     : https://prove2.me/theorems/349cc1dc-cc16-4d9c-bacc-2b3abf46450b
-- title:
--   Gauss b 20261113 b237 direct: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
open MeasureTheory Filter Topology

noncomputable section
theorem gauss_b_20261113_b237_direct_pointwise_upper_bound_7ef6c99e
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable
      (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable
      (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable
      (fun ω => (g m s ω - g p s ω)^2) ν)
    (hffOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable
      (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hClose : Tendsto (fun m =>
      ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hCauchy : Tendsto (fun mp : ℕ × ℕ =>
      ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) 
    : (∀ (m p : ℕ) (s : α), (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤
        3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) +
          ((∫ ω, (g m s ω - g p s ω)^2 ∂ν) +
           (∫ ω, (f p s ω - g p s ω)^2 ∂ν)))) := by sorry
end
