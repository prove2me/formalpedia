-- Prove2me | Theorems.Thm_nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate
-- name    : nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T07:49:42.896876+00:00
-- url     : https://prove2.me/theorems/2ac942bc-0ea3-48fb-8b30-5c7a6d92b027
-- statement:
--   This is the reverse `<=` direction of the Frobenius-duality rewrite for the tangent sampling deviation.
--
--   For $p\ge0$, every pairing
--   $$
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F
--   $$
--   with $\|X_1\|_F\le1$ is bounded by the scaled Frobenius norm appearing in `tangentSamplingDeviation`.  This is the Cauchy-Schwarz/dual-norm direction.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is rewritten as $\sup\langle X_1,Y(X_2)\rangle$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem nested_dual_supremum_le_tangent_sampling_deviation_of_nonnegative_rate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingNestedDualDeviation Omega S p ≤
      tangentSamplingDeviation Omega S p := by
  sorry
