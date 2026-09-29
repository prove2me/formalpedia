-- Prove2me | Theorems.Thm_tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
-- name    : tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:43:11.324361+00:00
-- url     : https://prove2.me/theorems/193fb02c-a2ec-446f-9c3e-4cf7b50b0534
-- statement:
--   This theorem dualizes the Frobenius norm inside the tangent sampling deviation while keeping the outer tangent-unit supremum separate.
--
--   For $p\ge0$,
--   $$
--   Z(\Omega)=\sup_{X_2\in T,\ \|X_2\|_F\le1}
--   p^{-1}\|P_TP_\Omega X_2-pX_2\|_F
--   $$
--   equals the nested dual supremum
--   $$
--   \sup_{X_2\in T,\ \|X_2\|_F\le1}
--   \sup_{\|X_1\|_F\le1}
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F.
--   $$
--   The condition $p\ge0$ is retained because the scalar $p^{-1}$ is outside the norm.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is rewritten as $\sup\langle X_1,Y(X_2)\rangle$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_nested_dual
open MatrixCompletion

theorem tangent_sampling_deviation_eq_nested_dual_supremum_of_nonnegative_rate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p =
      tangentSamplingNestedDualDeviation Omega S p := by
  sorry
