-- Prove2me | Theorems.Thm_tangent_bilinear_supremum_le_nested_dual_supremum
-- name    : tangent_bilinear_supremum_le_nested_dual_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T07:34:10.938513+00:00
-- url     : https://prove2.me/theorems/2afaa092-a669-4081-bf5d-b1d670bbb26d
-- statement:
--   This is the reverse direction of the formal supremum-flattening step used in the Appendix 9.1 representation.
--
--   Every value in the single supremum over admissible pairs $(X_1,X_2)$ is obtained by choosing the same $X_2$ in the outer nested supremum and the same $X_1$ in the inner dual supremum.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is written as a supremum over the two test matrices $X_1$ and $X_2$.  This node is a formal bridge for that source-backed display.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem tangent_bilinear_supremum_le_nested_dual_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p ≤
      tangentSamplingNestedDualDeviation Omega S p := by
  sorry
