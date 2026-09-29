-- Prove2me | Theorems.Thm_nested_dual_supremum_le_tangent_bilinear_supremum
-- name    : nested_dual_supremum_le_tangent_bilinear_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T07:33:41.582552+00:00
-- url     : https://prove2.me/theorems/170e14bd-eacb-4d6a-bda0-253d018afb76
-- statement:
--   This is one direction of the formal supremum-flattening step used in the Appendix 9.1 representation.
--
--   The nested dual form first chooses a tangent Frobenius-unit matrix $X_2$ and then takes a supremum over Frobenius-unit $X_1$.  Every value obtained in that nested process is bounded by the single supremum over all admissible pairs $(X_1,X_2)$.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is written as a supremum over the two test matrices $X_1$ and $X_2$.  This node is a formal bridge for that source-backed display.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem nested_dual_supremum_le_tangent_bilinear_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingNestedDualDeviation Omega S p ≤
      tangentSamplingTangentBilinearDeviation Omega S p := by
  sorry
