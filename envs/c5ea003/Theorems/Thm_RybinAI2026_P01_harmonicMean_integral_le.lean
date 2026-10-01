-- Prove2me | Theorems.Thm_RybinAI2026_P01_harmonicMean_integral_le
-- name    : RybinAI2026.P01.harmonicMean_integral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T07:28:37.293106+00:00
-- url     : https://prove2.me/theorems/a0f9c997-f580-4b37-aadf-7842f034d097
-- title:
--   Integral form of the harmonic-mean superadditivity (variance/Cauchy-Schwarz form)
-- statement:
--   For a finite measure mu and nonnegative f with strictly positive p, q, if the quotients f/p, f/q, f*q/(p*(p+q)) and f*(p+q)/(p*q) are integrable then (int f/(p+q)) * ((int f/p) + (int f/q)) <= (int f/p) * (int f/q). This is the integral form of the superadditivity of the harmonic mean: pointwise f/(p+q) = (f/p)(f/q)/((f/p)+(f/q)), and the gap is a variance, (int theta(1-theta)) * nu(1) <= (int theta)*(int (1-theta)) with theta = (1/p)/((1/p)+(1/q)).
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac. Reusable abstract engine: applied with mu = the norm-weighted sphere measure, f = |u.z|, p = u^T A u, q = u^T B u it yields the per-direction harmonic (mediant) bound F_{A+B}(z)*(F_A(z)+F_B(z)) <= F_A(z)*F_B(z), the u+v<=1 fact used by every P01 rank-one reduction. Proof: Cauchy-Schwarz via the discriminant 0 <= int (f/p - t sqrt(...))^2.

import Mathlib

open MeasureTheory Filter

namespace RybinAI2026.P01
theorem harmonicMean_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ]
    (f p q : α → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) (hf : ∀ x, 0 ≤ f x)
    (hip : Integrable (fun x => f x / p x) μ)
    (hiq : Integrable (fun x => f x / q x) μ)
    (hid : Integrable (fun x => f x * q x / (p x * (p x + q x))) μ)
    (him : Integrable (fun x => f x * (p x + q x) / (p x * q x)) μ) :
    (∫ x, f x / (p x + q x) ∂μ) * ((∫ x, f x / p x ∂μ) + (∫ x, f x / q x ∂μ))
      ≤ (∫ x, f x / p x ∂μ) * (∫ x, f x / q x ∂μ) := by
  sorry
end RybinAI2026.P01
