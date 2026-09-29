-- Prove2me | Theorems.Thm_centered_sampling_symmetrization_moment_bound_of_sample_ratio
-- name    : centered_sampling_symmetrization_moment_bound_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T18:32:52.904703+00:00
-- url     : https://prove2.me/theorems/d09ff53b-8fdb-4aaf-9357-d31b211c8b27
-- statement:
--   This is the sample-ratio-safe symmetrization estimate used in Section 6.1 of Candes-Recht.
--
--   For
--   $$
--   p=\frac{m}{n_1n_2},\qquad S_\Omega(X)=p^{-1}(P_\Omega-pI)X,
--   $$
--   assuming $0<n_1$, $0<n_2$, and $m\le n_1n_2$, there is a universal constant $C_{\rm sym}>0$ such that for every matrix $X$ and every integer $q\ge1$,
--   $$
--   \mathbb E_\Omega\,\|S_\Omega(X)\|^q
--   \le
--   C_{\rm sym}^q\,\mathbb E_\Omega\mathbb E_\varepsilon
--   \left\|p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top\right\|^q.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, equation (6.5), the Jensen independent-copy paragraph, the Rademacher symmetry of $\delta-\delta'$, and the displayed triangle-inequality estimate.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem centered_sampling_symmetrization_moment_bound_of_sample_ratio :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  sorry
