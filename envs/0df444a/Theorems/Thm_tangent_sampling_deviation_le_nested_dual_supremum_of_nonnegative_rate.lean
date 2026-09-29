-- Prove2me | Theorems.Thm_tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
-- name    : tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T07:49:14.451586+00:00
-- url     : https://prove2.me/theorems/2efcd9be-b39d-4526-92cd-7dd1e28dc495
-- statement:
--   This is the `<=` direction of the Frobenius-duality rewrite for the tangent sampling deviation.
--
--   For $p\ge0$, the scaled Frobenius norm in
--   $$
--   Z(\Omega)=\sup_{X_2\in T,\|X_2\|_F\le1}p^{-1}\|P_TP_\Omega X_2-pX_2\|_F
--   $$
--   is bounded by the nested dual supremum over Frobenius-unit test matrices $X_1$.  This is the direction that the dual unit ball has enough tests to recover the norm.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is rewritten as $\sup\langle X_1,Y(X_2)\rangle$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p ≤
      tangentSamplingNestedDualDeviation Omega S p := by
  sorry
