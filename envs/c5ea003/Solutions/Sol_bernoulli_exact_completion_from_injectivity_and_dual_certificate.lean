-- Prove2me | solution 1 for bernoulli_exact_completion_from_injectivity_and_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:09:20.165293+00:00
-- url     : https://prove2.me/submissions/1b01dac0-da49-43d9-a78b-52be7123e942

import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_success_probability_mono
import Theorems.Thm_dual_certificate_with_restricted_sampling_implies_unique_completion

open MatrixCompletion

/-- Intersect the high-probability injectivity and certificate events by a
Bernoulli union bound, then use the deterministic dual-certificate criterion to
embed that intersection into the exact-completion success event. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p cInjective cCertificate β : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < cInjective → 0 < cCertificate →
    bernoulliEventProb p (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
        1 - cInjective * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          StrictDualCertificate Omega S Y) ≥
        1 - cCertificate * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliSuccessProb p M ≥
        1 - (cInjective + cCertificate) *
          Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne _hcInjective _hcCertificate hInjectiveProb hCertificateProb
  have hIntersectionProb :=
    bernoulli_event_intersection_probability_from_lower_bounds
      p cInjective cCertificate (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega => SamplingOperatorInjectiveOnT Omega S)
      (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        StrictDualCertificate Omega S Y)
      hpNonneg hpLeOne hInjectiveProb hCertificateProb
  have hSuccessMono :
      bernoulliEventProb p
          (fun Omega =>
            SamplingOperatorInjectiveOnT Omega S ∧
              ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
                StrictDualCertificate Omega S Y) ≤
        bernoulliSuccessProb p M :=
    bernoulli_success_probability_mono p M
      (fun Omega =>
        SamplingOperatorInjectiveOnT Omega S ∧
          ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            StrictDualCertificate Omega S Y)
      hpNonneg hpLeOne
      (by
        intro Omega hGood
        exact dual_certificate_with_restricted_sampling_implies_unique_completion
          S Omega hGood.1 hGood.2)
  exact le_trans hIntersectionProb hSuccessMono

