-- Prove2me | Theorems.Thm_coordinate_tangent_supremum_eq_talagrand_supremum
-- name    : coordinate_tangent_supremum_eq_talagrand_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:32:02.464523+00:00
-- url     : https://prove2.me/theorems/23a857cd-c5aa-4259-a875-6047a6405666
-- statement:
--   This theorem removes the tangent restriction from the coordinate-expanded Talagrand supremum.
--
--   In the coordinate expression
--   $$
--   \sum_{i,j}(\delta_{ij}-p)p^{-1}
--   \langle X_1,P_T(e_i e_j^\top)\rangle_F
--   \langle P_T(e_i e_j^\top),X_2\rangle_F,
--   $$
--   the second test matrix appears only through its tangent projection.  Therefore the supremum over tangent $X_2$ with $\|X_2\|_F\le1$ agrees with the supremum over all Frobenius-unit $X_2$, using that $P_T$ is an orthogonal Frobenius contraction.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, the displayed supremum after equation (9.2), together with standard orthogonal-projection facts for $P_T$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_coordinate_tangent
open MatrixCompletion

theorem coordinate_tangent_supremum_eq_talagrand_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingCoordinateTangentSupremumDeviation Omega S p =
      tangentSamplingTalagrandSupremumDeviation Omega S p := by
  sorry
