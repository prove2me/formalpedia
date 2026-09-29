-- Prove2me | solution 1 for linear_neumann_correction_from_diagonal_off_diagonal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:45:01.197831+00:00
-- url     : https://prove2.me/submissions/2497598b-202e-43d6-805b-09a8524831fc

import Theorems.Thm_linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono

open MatrixCompletion

/-- Intersect the diagonal and off-diagonal good events, then use the
deterministic (6.8) decomposition plus the spectral-norm triangle inequality. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p Cdiag Coff cdiag coff β lam : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < cdiag → 0 < coff →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
            Cdiag * Real.rpow lam (-1)) ≥
        1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
            Coff * Real.rpow lam (-1)) ≥
        1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          NeumannCertificateTermSpectralBound Omega S p 1
            ((Cdiag + Coff) * Real.rpow lam (-1))) ≥
        1 - (cdiag + coff) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne _hcdiag _hcoff hDiagProb hOffProb
  have hIntersectionProb :=
    bernoulli_event_intersection_probability_from_lower_bounds
      p cdiag coff (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega =>
        spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
          Cdiag * Real.rpow lam (-1))
      (fun Omega =>
        spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
          Coff * Real.rpow lam (-1))
      hpNonneg hpLeOne hDiagProb hOffProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
                Cdiag * Real.rpow lam (-1) ∧
              spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
                Coff * Real.rpow lam (-1)) ≤
        bernoulliEventProb p
          (fun Omega =>
            NeumannCertificateTermSpectralBound Omega S p 1
              ((Cdiag + Coff) * Real.rpow lam (-1))) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
            Cdiag * Real.rpow lam (-1) ∧
          spectralNorm (linearNeumannOffDiagonalContribution Omega S p) ≤
            Coff * Real.rpow lam (-1))
      (fun Omega =>
        NeumannCertificateTermSpectralBound Omega S p 1
          ((Cdiag + Coff) * Real.rpow lam (-1)))
      hpNonneg hpLeOne
      (by
        intro Omega hBounds
        exact linear_neumann_correction_bound_from_diagonal_off_diagonal_bounds
          S Omega p Cdiag Coff lam hBounds.1 hBounds.2)
  exact le_trans hIntersectionProb hMono

