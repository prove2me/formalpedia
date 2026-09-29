-- Prove2me | solution 1 for rademacher_sampled_matrix_conditional_khintchine_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:01:58.490343+00:00
-- url     : https://prove2.me/submissions/f1ed2fb2-d293-4115-9ab6-bedb813fdba5

import Theorems.Thm_rademacher_sampled_matrix_conditional_khintchine_bound
import Theorems.Thm_spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_bound

open MatrixCompletion

/-- Conditional Theorem 6.3 Khintchine step: compare spectral moments to
Schatten moments, apply the noncommutative Khintchine inequality, and unfold
the coordinate-series row/column variance scale. -/
theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q := by
  rcases rademacher_sampled_matrix_schatten_moment_khintchine_bound with
    ⟨Ckh, hCkh, hKhintchine⟩
  refine ⟨Ckh, hCkh, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hqOne hqLog
  have hSpectralToSchatten :=
    spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix
      β hβ n₁ n₂ m q Omega X hqOne hqLog
  have hSchatten :=
    hKhintchine β hβ n₁ n₂ m q Omega X hqOne hqLog
  exact by
    simpa [rademacherSampledVarianceScale, mul_assoc] using
      le_trans hSpectralToSchatten hSchatten

