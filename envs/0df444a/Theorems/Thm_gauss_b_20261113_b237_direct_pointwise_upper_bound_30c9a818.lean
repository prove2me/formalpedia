-- Prove2me | Theorems.Thm_gauss_b_20261113_b237_direct_pointwise_upper_bound_30c9a818
-- name    : gauss_b_20261113_b237_direct_pointwise_upper_bound_30c9a818
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T11:20:26.037193+00:00
-- url     : https://prove2.me/theorems/d0a387ac-de04-429b-8d73-f1d08f085456
-- title:
--   Gauss b 20261113 b237 direct: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
open MeasureTheory Filter Topology

noncomputable section
theorem gauss_b_20261113_b237_direct_pointwise_upper_bound_30c9a818
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
    (hInner : (let E : ℕ → ℝ := (fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ); let G : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ); let F : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (f mp.1 s ω - f mp.2 s ω)^2 ∂ν) ∂μ); (∀ (m p : ℕ) (s : α), (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤
        3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) +
          ((∫ ω, (g m s ω - g p s ω)^2 ∂ν) +
           (∫ ω, (f p s ω - g p s ω)^2 ∂ν))))))
    : (let E : ℕ → ℝ := (fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ); let G : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ); let F : ℕ × ℕ → ℝ := (fun mp => ∫ s, (∫ ω, (f mp.1 s ω - f mp.2 s ω)^2 ∂ν) ∂μ); (∀ (m p : ℕ), F (m,p) ≤ 3 * (E m + (G (m,p) + E p)))) := by sorry
end
