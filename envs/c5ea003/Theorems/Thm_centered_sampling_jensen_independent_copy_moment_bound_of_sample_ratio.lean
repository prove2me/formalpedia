-- Prove2me | Theorems.Thm_centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
-- name    : centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T18:30:53.688427+00:00
-- url     : https://prove2.me/theorems/6585113d-18c8-4106-b87c-18196b77d0cf
-- statement:
--   This is the integrated Jensen independent-copy estimate from Section 6.1 of Candes-Recht, stated with the sample-ratio side conditions that make the Bernoulli weights nonnegative.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad S_\Omega(X)=p^{-1}(P_\Omega-pI)X.
--   $$
--   If $0<n_1$, $0<n_2$, $m\le n_1n_2$, and $q\ge1$, then for every fixed matrix $X$
--   $$
--   \mathbb E_\Omega\,\|S_\Omega(X)\|^q
--   \le
--   \mathbb E_{\Omega,\Omega'}\,\|S_\Omega(X)-S_{\Omega'}(X)\|^q,
--   $$
--   where $\Omega'$ is an independent Bernoulli sample with the same inclusion probability $p$.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, equation (6.5) and the Jensen independent-copy paragraph immediately following it.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                centeredSamplingFluctuation Omega'
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  sorry
