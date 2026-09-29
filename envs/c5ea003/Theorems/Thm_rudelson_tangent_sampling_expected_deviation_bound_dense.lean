-- Prove2me | Theorems.Thm_rudelson_tangent_sampling_expected_deviation_bound_dense
-- name    : rudelson_tangent_sampling_expected_deviation_bound_dense
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T15:44:26.578331+00:00
-- url     : https://prove2.me/theorems/a098d77c-d903-4ecf-8d2c-aee8d5215a28
-- statement:
--   Corrected (sampling-density) variant of `rudelson_tangent_sampling_expected_deviation_bound` (DISPROVED as stated — false without a density hypothesis). Candès–Recht 2009, Thm 4.2 eq (4.9), $\beta$-scale form: there is a universal constant $C>0$ such that for every $\beta>2$ and every rank-$r$ matrix with coherence hypotheses A0($\mu_0$) and A1($\mu_1$), **provided** $m \ge \beta\,\mu_0\,(\max n_1 n_2)\,r\,\log(\max n_1 n_2)$, the expected tangent sampling deviation $\mathbb{E}\,p^{-1}\|P_TP_\Omega P_T-pP_T\|$ is at most $C\,\sqrt{\mu_0\,(\max n_1 n_2)\,r\,(\beta\log(\max n_1 n_2))/m}$. The density hypothesis (matching the paper's side condition, Thm 4.1 eq (4.5)/Thm 4.2 eq (4.9), p.18) excludes the maximal-coherence low-sample counterexample that disproved the un-hypothesized ancestor.
-- source:
--   Candès & Recht, "Exact Matrix Completion via Convex Optimization", arXiv:0805.4471 (2009), Thm 4.1 eq (4.5) & Thm 4.2 eq (4.9), p.18; proof via Section 6 (noncommutative Khintchine moment method, Lemma 6.1, p.24).

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_tangent_sampling_expected_deviation_bound_dense :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m := by sorry
