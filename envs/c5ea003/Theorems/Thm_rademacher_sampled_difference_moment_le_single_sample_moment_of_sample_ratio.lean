-- Prove2me | Theorems.Thm_rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
-- name    : rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:11:31.906347+00:00
-- url     : https://prove2.me/theorems/d957293e-dc5e-45e4-a411-4d06cf1ba239
-- statement:
--   This is the sample-ratio-safe triangle/Minkowski estimate for the Rademacher-signed difference in Candes-Recht Section 6.1.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad S_{\Omega,\varepsilon}(X)=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top.
--   $$
--   Assume $0<n_1$, $0<n_2$, $m\le n_1n_2$, and $q\ge1$. There is a universal constant $C_{\rm sym}>0$ such that
--   $$
--   \mathbb E_{\Omega,\Omega'}\mathbb E_\varepsilon\,\|S_{\Omega,\varepsilon}(X)-S_{\Omega',\varepsilon}(X)\|^q
--   \le
--   C_{\rm sym}^q\,\mathbb E_{\Omega}\mathbb E_\varepsilon\,\|S_{\Omega,\varepsilon}(X)\|^q.
--   $$
--   This is the formal version of the triangle-inequality step that replaces the signed two-copy difference by one signed sampled copy.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, the displayed triangle-inequality estimate following the Rademacher representation.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega Omega' =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                      rademacherSampledMatrix Omega' eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  sorry
