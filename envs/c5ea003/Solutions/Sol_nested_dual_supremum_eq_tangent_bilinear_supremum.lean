-- Prove2me | solution 1 for nested_dual_supremum_eq_tangent_bilinear_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T07:34:13.243353+00:00
-- url     : https://prove2.me/submissions/9c7a815a-01a2-457c-b45a-bbba5bda2c5f

import Theorems.Thm_nested_dual_supremum_le_tangent_bilinear_supremum
import Theorems.Thm_tangent_bilinear_supremum_le_nested_dual_supremum

open MatrixCompletion

/-- Formal flattening of the two suprema in the Appendix 9.1 display.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the expression is written as a supremum over the two test matrices
`X_1` and `X_2`.  The imported children prove the two order directions for
flattening the nested supremum into a single supremum over pairs. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingNestedDualDeviation Omega S p =
      tangentSamplingTangentBilinearDeviation Omega S p := by
  exact le_antisymm
    (nested_dual_supremum_le_tangent_bilinear_supremum Omega S p)
    (tangent_bilinear_supremum_le_nested_dual_supremum Omega S p)
