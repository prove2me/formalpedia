-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
-- name    : linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:41:19.818906+00:00
-- url     : https://prove2.me/theorems/550a010a-a643-4952-88b4-3674b73b8a67
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion

/-- Fixed-coordinate two-term scalar Bernstein tail for the corrected
rectangular Lemma 6.6 base bounds.

For one output coordinate `w`, the coefficient entry is represented as a
centered scalar sampling fluctuation of the fixed base matrix
`linearNeumannOffDiagonalCoefficientBaseMatrix S w`.  Applying the raw scalar
Bernstein inequality gives a two-term threshold with the corrected
`min(n₁,n₂)` base-matrix scales.  No range-term absorption is performed here.

Source: Candès--Recht 2008, Section 6.2, PDF pp. 27--28, Lemma 6.6,
equations (6.15)--(6.17), with the rectangular convention after equations
(6.2)--(6.4). -/

theorem linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ C' : ℝ,
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
        ∀ w : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannOffDiagonalCoefficientBaseMatrix S w))) →
        entrySupNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        frobeniusNorm
            (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
          Cfro * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
                Cpoint *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cfro * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Centry * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
  sorry
