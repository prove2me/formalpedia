-- Prove2me | Theorems.Thm_fixed_matrix_centered_sampling_log_moment_bound_of_two_sample_lower
-- name    : fixed_matrix_centered_sampling_log_moment_bound_of_two_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T08:41:27.032024+00:00
-- url     : https://prove2.me/theorems/c978266f-5bcf-497d-b438-575f3eb60a37
-- statement:
--   Corrected fixed-matrix centered-sampling log-moment estimate, matching the source proof with the exponent window made explicit.
--
--   Let $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$.  Under
--   $$
--   1\le \beta\log n,\qquad m\ge 2\beta n\log n,
--   $$
--   the theorem chooses an integer moment exponent $q$ with $q\ge \beta\log n$ and proves
--   $$
--   \mathbb E_\Omega\,\|p^{-1}(P_\Omega-pI)X\|^q
--   \le
--   \left(C\sqrt{\frac{\beta n\log n}{p}}\,\|X\|_\infty\right)^q.
--   $$
--   The extra displayed hypotheses are not cosmetic: they expose the integer exponent window needed by Lemma 6.2, especially the condition $q\le pn$ used in the row/column energy moment estimate.
--
--   Source: Candes-Recht 2008, PDF pp. 24-25, Section 6.1, equation (6.5), Lemma 6.2/equation (6.6), and Theorem 6.3/equation (6.7).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem fixed_matrix_centered_sampling_log_moment_bound_of_two_sample_lower :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (1 : ℝ) ≤ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ 2 * β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (C * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  sorry
