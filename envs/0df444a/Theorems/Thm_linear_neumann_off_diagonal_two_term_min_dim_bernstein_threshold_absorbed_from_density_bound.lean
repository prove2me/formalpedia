-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound
-- name    : linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:44:00.953753+00:00
-- url     : https://prove2.me/theorems/34ebd1e9-f277-40dd-8f24-46dd3ea11e3f
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion

/-- Scalar absorption for the corrected rectangular two-term Bernstein
threshold, assuming the Lemma 6.6 density proviso directly.

This is the pure post-(6.17) arithmetic step: after scalar Bernstein gives a
Frobenius/variance term and an entry-sup/range term, the density lower bound
`m ≥ const * μ₀ * N * r * β log N`, with `N = max(n₁,n₂)`, absorbs the range
term into the final Lemma 6.6 coefficient scale.  The deterministic base
matrix estimates use `min(n₁,n₂)`.

Source: Candès--Recht 2008, Section 6.2, PDF p. 28, equation (6.17) and the
paragraph immediately following it. -/

theorem linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_from_density_bound
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ Ccoef' : ℝ, Ccoef ≤ Ccoef' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          ((8 : ℝ) / 3) * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
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
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) ≤
          Ccoef' * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  sorry
