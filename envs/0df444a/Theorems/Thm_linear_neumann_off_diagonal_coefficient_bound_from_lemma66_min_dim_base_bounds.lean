-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds
-- name    : linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:47:32.970061+00:00
-- url     : https://prove2.me/theorems/22f4a0e7-80ce-482c-9574-275e477a65eb
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion

/-- Source-faithful rectangular Lemma 6.6 coefficient event from corrected
base-matrix bounds.

This theorem packages exactly the scalar Bernstein and coordinate-union-bound
content of Candès--Recht Lemma 6.6 for the first off-diagonal Neumann
coefficient matrix `Q(E)`: each coefficient entry is a centered scalar
sampling fluctuation of the fixed base matrix
`linearNeumannOffDiagonalCoefficientBaseMatrix S w`, whose entry and
Frobenius/variance bounds are supplied as hypotheses.  The base bounds use the
rectangular `min(n₁,n₂)` kernel scale, while the final probability and sample
complexity use the ambient `max(n₁,n₂)` scale.

Source: Candès--Recht 2008, Section 6.2, PDF pp. 27--29, equations
(6.13)--(6.17), with the rectangular convention after equations (6.2)--(6.4)
and the global Theorem 1.3 sample lower bound from equation (1.9). -/

theorem linear_neumann_off_diagonal_coefficient_bound_from_lemma66_min_dim_base_bounds
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w : Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        (∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
