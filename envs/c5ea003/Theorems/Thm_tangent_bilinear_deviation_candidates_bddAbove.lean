-- Prove2me | Theorems.Thm_tangent_bilinear_deviation_candidates_bddAbove
-- name    : tangent_bilinear_deviation_candidates_bddAbove
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T08:20:53.83906+00:00
-- url     : https://prove2.me/theorems/7d62abc2-efb4-4b72-bc26-5c833bd2a41f
-- statement:
--   This theorem is the boundedness input for flattening the nested Frobenius-dual supremum in Appendix 9.1.
--
--   For fixed sampling set $\Omega$, SVD data $S$, and scalar $p\in\mathbb R$, consider the set of bilinear values
--   $$
--   p^{-1}\langle X_1, P_TP_\Omega X_2-pX_2\rangle_F
--   $$
--   where $\|X_1\|_F\le1$, $X_2\in T$, and $\|X_2\|_F\le1$.  The theorem says that this set is bounded above, so its real supremum is legitimate in Lean.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2).  The paper moves from the nested dual form of $Z$ to a single supremum over two test matrices; this formal node isolates the finite-dimensional boundedness fact hidden in that passage.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion
open scoped Classical BigOperators

theorem tangent_bilinear_deviation_candidates_bddAbove
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    BddAbove {v : ℝ |
      ∃ X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧
          tangentProjection S X2 = X2 ∧
            frobeniusNorm X2 ≤ 1 ∧
              v =
                p⁻¹ *
                  matrixInner X1
                    (tangentProjection S (samplingProjection Omega X2) - p • X2)} := by
  sorry
