-- Prove2me | Theorems.Thm_avram_gaussb_20261113_gb_b237_stability_pointwise_upper_bound_e5a13c33
-- name    : avram_gaussb_20261113_gb_b237_stability_pointwise_upper_bound_e5a13c33
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T13:10:25.344952+00:00
-- url     : https://prove2.me/theorems/eabf9d20-77d9-449d-9d3c-929d86095a11
-- title:
--   Avram gaussb 20261113 gb b237 stability: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
open MeasureTheory Filter Topology

noncomputable section
theorem avram_gaussb_20261113_gb_b237_stability_pointwise_upper_bound_e5a13c33
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
    : (let V : ℕ → ℝ := (fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ); let W : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ); (∀ (m p : ℕ), (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤
      3 * (V m + W (m, p) + V p))) := by sorry
end
