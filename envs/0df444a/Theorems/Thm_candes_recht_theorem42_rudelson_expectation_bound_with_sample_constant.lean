-- Prove2me | Theorems.Thm_candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant
-- name    : candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T02:59:21.384407+00:00
-- url     : https://prove2.me/theorems/e0c95c99-31f8-4dba-aace-327f70fbde8d
-- statement:
--   This theorem is the Rudelson expectation half of Candes-Recht Theorem 4.2, repaired so that the paper's smallness proviso is part of the formal statement.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),\qquad
--   Z(\Omega)=p^{-1}\left\|P_TP_\Omega P_T-pP_T\right\|.
--   $$
--   The matrix $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, the object $S$ records its singular-vector data, and $A0(S,\mu_0)$ is the Candes-Recht incoherence assumption controlling the spread of the singular vector spaces.
--
--   Equation (4.9) gives the expectation estimate
--   $$
--   \mathbb E_p Z\le C\sqrt{\frac{\mu_0 n r\log n}{m}},
--   $$
--   but only when that right-hand side is smaller than $1$.  Therefore this node asks for the version actually needed downstream: if
--   $$
--   m\ge C'\mu_0 n r\,\beta\log n,\qquad \beta>2,
--   $$
--   then both
--   $$
--   \mathbb E_p Z\le C\sqrt{\frac{\mu_0 n r\,\beta\log n}{m}}
--   \quad\text{and}\quad
--   \mathbb E_p Z\le1
--   $$
--   hold.  The second conclusion is essential because the Talagrand half of Theorem 4.2, equation (4.10), begins with the hypothesis $\mathbb E Z\le1$.
--
--   Source location: Candes-Recht 2008, PDF pp. 18--19, Theorem 4.2, equations (4.8)--(4.9), especially the proviso after equation (4.9).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
            tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 := by
  sorry
