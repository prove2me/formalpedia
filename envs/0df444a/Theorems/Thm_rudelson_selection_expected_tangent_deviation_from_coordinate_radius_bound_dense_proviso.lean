-- Prove2me | Theorems.Thm_rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
-- name    : rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T02:13:43.667807+00:00
-- url     : https://prove2.me/theorems/b04126d3-720e-4d7f-83c9-3b827133b569
-- statement:
--   Corrected Rudelson selection estimate (expected tangent-sampling deviation) WITH the Candès–Recht Theorem 4.2 “right-hand side $\le 1$” proviso. There is an absolute constant $C_{sel}>0$ such that for every $\beta>2$, all sizes with $m\le n_1n_2$, every reduced SVD $S$ of $M$, and every radius $R\ge 0$: if the sampling is dense, $m\ge\beta\,(\max n)\,r\,\log(\max n)$, if the desymmetrization parameter is bounded, $\sqrt{\log(\max n)/p}\cdot R\le 1$ (with $p=m/(n_1n_2)$), and if every tangent-coordinate projection has Frobenius norm at most $R$, then the expected tangent-sampling deviation $\mathbb{E}_\Omega\,p^{-1}\|P_TP_\Omega P_T-pP_T\|$ is at most $C_{sel}\,\sqrt{\log(\max n)/p}\,R$. The added proviso $\sqrt{\log/p}\cdot R\le 1$ is exactly Candès–Recht 2009, Theorem 4.2 part 1 (eq. (4.9), p.18): “provided the right-hand side is smaller than 1.” It comes from the self-bounding desymmetrization $\mathbb{E}Z\le A+A\sqrt{\mathbb{E}Z}$ with $A=\sqrt{\log/p}\,R$, which yields the linear bound only when $A\le 1$; without it the stated linear bound can fail (the true bound is $\sim A^2$ when $A\ge 1$). This corrects the radius_dense node which omitted the proviso (R a free parameter).
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Theorem 4.2 part 1, eq. (4.9), p.18 (“provided the RHS is smaller than 1”); self-bounding desymmetrization of the Rudelson–Candès–Tao expectation bound.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso :
    ∃ Csel : ℝ, 0 < Csel ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        Real.sqrt
            (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R ≤ 1 →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            R := by sorry
