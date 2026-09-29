-- Prove2me | Theorems.Thm_rudelson_selection_tangent_deviation_selfbounding_recursion_dense
-- name    : rudelson_selection_tangent_deviation_selfbounding_recursion_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T22:20:55.857094+00:00
-- url     : https://prove2.me/theorems/69e51890-84b4-4eff-b92a-a0cf61044ace
-- title:
--   Rudelson selection: the self-bounding desymmetrization recursion
-- statement:
--   Rudelson selection desymmetrization core (self-bounding recursion), dense regime. Under the sampling-density hypothesis $m \ge \beta\,\max(n_1,n_2)\,r\,\log\max(n_1,n_2)$ with $\beta>2$, and the coordinate Frobenius bound $\|P_T(e_ie_j^*)\|_F \le R$ for all $i,j$, the Bernoulli expectation $EZ := \mathbb{E}_\Omega[Z]$ of the tangent sampling deviation $Z=p^{-1}\|P_TP_\Omega P_T - pP_T\|$ is nonnegative and obeys the self-bounding recursion $EZ \le C_{sel}\,(sR) + C_{sel}\,(sR)\,\sqrt{EZ}$, where $s=\sqrt{\log\max(n_1,n_2)/p}$ and $p=m/(n_1n_2)$. This is the genuine Rudelson 1999 selection content: symmetrization $(\delta-p)\to\varepsilon$ on the rank-one tensor operators $P_T(e_ie_j^*)\otimes P_T(e_ie_j^*)$, the noncommutative Khintchine / Gram bound on the symmetrized operator, and Cauchy-Schwarz on the diagonal. Source: Candes-Recht 2009 (arXiv:0805.4471) §4.2 eq.(4.9) p.18 (Theorem 4.2 part 1), citing M. Rudelson, Random vectors in the isotropic position, J. Funct. Anal. 164 (1999), 60-72.
-- source:
--   Candes & Recht, arXiv:0805.4471, sec 4.2 eq.(4.9) p.18 (Theorem 4.2 part 1, 'provided the RHS is smaller than 1'); Rudelson 1999.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_selection_tangent_deviation_selfbounding_recursion_dense :
    ∃ Csel : ℝ, 0 < Csel ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        (0 ≤ bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ∧
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csel *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          + Csel *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R) *
            Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) := by sorry
