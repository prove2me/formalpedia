-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
-- name    : linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:46:18.038969+00:00
-- url     : https://prove2.me/theorems/6f075ea1-40f5-4e44-9a63-861de193b10b
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion

/-- Scalar absorption for the corrected rectangular two-term Bernstein
threshold in Lemma 6.6 under the full Theorem 1.3 sample lower bound.

After equation (6.17), Candès--Recht uses the density proviso
`n p ≥ const * μ₀ r β log n` to absorb the entry-sup/range term into the same
scale as the Frobenius/variance term.  In the rectangular formalization the
base matrix estimates use `min(n₁,n₂)`, while the final Lemma 6.6 display uses
`N = max(n₁,n₂)`.

Source: Candès--Recht 2008, Section 6.2, PDF p. 28, equation (6.17) and the
paragraph immediately following it, with the Theorem 1.3 sample lower bound
from equation (1.9). -/

theorem linear_neumann_off_diagonal_two_term_min_dim_bernstein_threshold_absorbed_under_general_sample_bound
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
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
          Ccoef * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  sorry
