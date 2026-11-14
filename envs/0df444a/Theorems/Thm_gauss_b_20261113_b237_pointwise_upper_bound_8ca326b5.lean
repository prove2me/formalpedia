-- Prove2me | Theorems.Thm_gauss_b_20261113_b237_pointwise_upper_bound_8ca326b5
-- name    : gauss_b_20261113_b237_pointwise_upper_bound_8ca326b5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T08:40:31.838206+00:00
-- url     : https://prove2.me/theorems/57f235e7-740b-41ea-acb6-b29b8dce02d5
-- title:
--   Gauss b 20261113 b237: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
open MeasureTheory Filter Topology

noncomputable section
theorem gauss_b_20261113_b237_pointwise_upper_bound_8ca326b5
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
    (hTri : (∀ (a b c : ℝ), (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2)))
    : (∀ (m p : ℕ), (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤
      3 * ((∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ) +
        (∫ s, (∫ ω, (g m s ω - g p s ω)^2 ∂ν) ∂μ) +
        (∫ s, (∫ ω, (f p s ω - g p s ω)^2 ∂ν) ∂μ))) := by sorry
end
