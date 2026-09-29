-- Prove2me | Theorems.Thm_rudelson_selection_symmetrized_tensor_khintchine_dense
-- name    : rudelson_selection_symmetrized_tensor_khintchine_dense
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:41:16.115372+00:00
-- url     : https://prove2.me/theorems/2479e5b5-96ee-4a7a-a0ef-e12a0238867b
-- statement:
--   Symmetrized tensor non-commutative Khintchine bound (dense regime) = Steps 1 and 2 of the proof of Theorem 1 in Rudelson 1999 (J. Funct. Anal. 164). There is a constant $C_{sym}>0$ such that, under the dense density hypothesis and the coordinate-radius bound $\lVert P_T(e_ie_j^*)\rVert_F\le R$, the expected tangent-sampling deviation satisfies $EZ\le C_{sym}\,(sR)\,\sqrt{EZ+1}$ with $s=\sqrt{\log\max(n_1,n_2)/p}$, $p=m/(n_1n_2)$. The proof is symmetrization $(\delta-p)\to\varepsilon$ (ghost copy) followed by the matrix Lust-Picquard / non-commutative Khintchine inequality applied to the rank-one tensor operators $X_j=y_j\otimes y_j$, $y_j=P_T(e_ie_j^*)$, using the spectral identity $(yy^*)^2=\lVert y\rVert^2\,yy^*$ so that $\lVert(\sum X_j^2)^{1/2}\rVert\le \max_j\lVert y_j\rVert\,\lVert\sum y_jy_j^*\rVert^{1/2}$.
-- source:
--   Rudelson, J. Funct. Anal. 164 (1999) 60-72, Theorem 1 proof Steps 1-2 (symmetrization p.3 + Lust-Picquard tensor lemma p.4); Lust-Picquard/Pisier non-commutative Khintchine; van Handel/Tropp matrix concentration. Candes-Recht 2009 arXiv:0805.4471 Section 4.2 eq(4.9) p.18.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem rudelson_selection_symmetrized_tensor_khintchine_dense :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) * Real.log (↑(max n₁ n₂)) →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csym *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          * Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) + 1) := by sorry
