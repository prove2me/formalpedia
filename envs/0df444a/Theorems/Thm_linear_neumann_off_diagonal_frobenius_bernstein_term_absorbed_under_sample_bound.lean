-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_frobenius_bernstein_term_absorbed_under_sample_bound
-- name    : linear_neumann_off_diagonal_frobenius_bernstein_term_absorbed_under_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T16:16:55.323554+00:00
-- url     : https://prove2.me/theorems/1ad627c3-4d12-436c-86b1-567f3f16cd10
-- statement:
--   This is the Frobenius/variance half of the scalar absorption after Candes--Recht equation (6.17).
--
--   After substituting the base-matrix Frobenius scale
--   $$
--   F=C_{\rm fro}\mu_1\sqrt{\frac r{n_1n_2}}\sqrt{\frac{\mu_0r}{n}},\qquad n=\max(n_1,n_2),
--   $$
--   the theorem says that
--   $$
--   C_{\rm two}\sqrt{\frac{(\beta+2)\log n}{p}}\,F
--   \le C_F\mu_1\sqrt{\frac r{n_1n_2}}\sqrt{\frac{\mu_0nr\,\beta\log n}{m}},
--   \qquad p=\frac{m}{n_1n_2}.
--   $$
--   This is the variance summand in the two-term Bernstein threshold. Source location: Candes--Recht, Section 6.2, Lemma 6.6, equation (6.17) and the paragraph immediately following it.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_frobenius_bernstein_term_absorbed_under_sample_bound
    (Ctwo Cfro : ℝ) :
    0 < Ctwo → 0 < Cfro →
    ∃ Cfrob : ℝ, 0 < Cfrob ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))) ≤
          Cfrob * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  sorry
