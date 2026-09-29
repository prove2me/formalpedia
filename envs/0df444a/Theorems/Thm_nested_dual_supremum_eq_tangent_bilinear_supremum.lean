-- Prove2me | Theorems.Thm_nested_dual_supremum_eq_tangent_bilinear_supremum
-- name    : nested_dual_supremum_eq_tangent_bilinear_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T07:00:58.713524+00:00
-- url     : https://prove2.me/theorems/36d295c0-5e23-4637-812e-9fbed3e3d5d0
-- statement:
--   This theorem flattens the nested Frobenius-dual supremum into the pair supremum used by the tangent bilinear representation.
--
--   It states that
--   $$
--   \sup_{X_2\in T,\|X_2\|_F\le1}\sup_{\|X_1\|_F\le1}
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F
--   $$
--   is the same as the single supremum over pairs $(X_1,X_2)$ satisfying the same constraints.  This is formal supremum bookkeeping, separated so that the analytic Frobenius-duality step remains reusable.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, the displayed equality $Z=\sup\langle X_1,Y(X_2)\rangle$ after equation (9.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem nested_dual_supremum_eq_tangent_bilinear_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingNestedDualDeviation Omega S p =
      tangentSamplingTangentBilinearDeviation Omega S p := by
  sorry
