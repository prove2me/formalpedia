-- Prove2me | Theorems.Thm_tangent_bilinear_supremum_eq_coordinate_tangent_supremum
-- name    : tangent_bilinear_supremum_eq_coordinate_tangent_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:31:32.449645+00:00
-- url     : https://prove2.me/theorems/72032b6c-0cd5-44d3-adc5-f30a6d8958ab
-- statement:
--   This theorem is the coordinate-expansion step of the Appendix 9.1 representation.
--
--   Starting from the tangent-restricted bilinear expression
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F,
--   $$
--   expand $P_\Omega$ in the coordinate basis.  The result is the coordinate sum
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   \sum_{i,j}(\delta_{ij}-p)p^{-1}
--   \langle X_1,P_T(e_i e_j^\top)\rangle_F
--   \langle P_T(e_i e_j^\top),X_2\rangle_F.
--   $$
--   This child keeps the tangent restriction on $X_2$; removing that restriction is a separate projection/supremum theorem.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_coordinate_tangent
open MatrixCompletion

theorem tangent_bilinear_supremum_eq_coordinate_tangent_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p =
      tangentSamplingCoordinateTangentSupremumDeviation Omega S p := by
  sorry
