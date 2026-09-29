-- Prove2me | Theorems.Thm_rudelson_selection_expected_tangent_deviation_from_coordinate_bound_dense
-- name    : rudelson_selection_expected_tangent_deviation_from_coordinate_bound_dense
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T15:44:02.473791+00:00
-- url     : https://prove2.me/theorems/43b949c7-fa00-4eda-8d0a-46b803ffb0b1
-- statement:
--   Corrected (sampling-density) variant of `rudelson_selection_expected_tangent_deviation_from_coordinate_bound` (DISPROVED as stated — false without a density hypothesis). Candès–Recht 2009, Thm 4.2 eq (4.9): there is a universal constant $C>0$ such that for every $\beta>2$ and every rank-$r$ matrix satisfying the coordinate Frobenius bound $\|P_T(e_ie_j^*)\|_F^2 \le 2\mu_0 r/\max(n_1,n_2)$ with $\mu_0\ge1$, **provided the sampling density satisfies** $m \ge \beta\,\mu_0\,(\max n_1 n_2)\,r\,\log(\max n_1 n_2)$, the expected tangent sampling deviation $\mathbb{E}\,p^{-1}\|P_TP_\Omega P_T-pP_T\|$ ($p=m/(n_1n_2)$) is at most $C\,\sqrt{\mu_0\,(\max n_1 n_2)\,r\,\log(\max n_1 n_2)/m}$. The density hypothesis (the paper's 'provided $C_R\sqrt{\mu_0 n r\beta\log n/m}<1$' side condition, Thm 4.1 eq (4.5), p.18) is exactly what excludes the maximal-coherence low-sample counterexample ($n_1=n_2=N$, $u_1=v_1=e_0$, $m=N$) that disproved the un-hypothesized ancestor.
-- source:
--   Candès & Recht, "Exact Matrix Completion via Convex Optimization", arXiv:0805.4471 (2009), Thm 4.1 eq (4.5) & Thm 4.2 eq (4.9), p.18; proof via Section 6 (noncommutative Khintchine moment method, Lemma 6.1, p.24).

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_selection_expected_tangent_deviation_from_coordinate_bound_dense :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        TangentCoordinateFrobeniusBound S
          (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by sorry
