-- Prove2me | Theorems.Thm_centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
-- name    : centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:02:14.890773+00:00
-- url     : https://prove2.me/theorems/a8e5cd3e-4a52-46a2-b112-9bdcfc9e1a86
-- statement:
--   This is the pointwise Jensen step in the independent-copy symmetrization argument of Candes-Recht Section 6.1.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad S_\Omega(X)=p^{-1}(P_\Omega-pI)X.
--   $$
--   Assume $0<n_1$, $0<n_2$, and $m\le n_1n_2$, so $p\in[0,1]$ is a genuine Bernoulli sampling probability. For every fixed observation set $\Omega$, every matrix $X$, and every integer $q\ge1$, Jensen's inequality applied to an independent copy $\Omega'$ gives
--   $$
--   \|S_\Omega(X)\|^q
--   \le
--   \mathbb E_{\Omega'}\,\|S_\Omega(X)-S_{\Omega'}(X)\|^q.
--   $$
--   The reason is that the centered sampling fluctuation has mean zero, so
--   $$
--   S_\Omega(X)=\mathbb E_{\Omega'}\bigl[S_\Omega(X)-S_{\Omega'}(X)\bigr],
--   $$
--   and the function $A\mapsto\|A\|^q$ is convex for $q\ge1$.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, equation (6.5) and the paragraph applying Jensen's inequality to $f(S)=\|S\|^q$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        spectralNorm
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q ≤
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega' =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                  centeredSamplingFluctuation Omega'
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  sorry
