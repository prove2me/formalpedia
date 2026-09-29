-- Prove2me | Theorems.Thm_entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
-- name    : entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:10:27.015506+00:00
-- url     : https://prove2.me/theorems/90e7678d-1270-4af9-a372-97997a9af208
-- statement:
--   This is a finite-dimensional algebra lemma for the all-equal quadratic Neumann base matrix.
--
--   If the sign matrix satisfies $\|E\|_\infty\le B_E$ and the diagonal tangent-coordinate kernel satisfies
--   $$
--   \left|\left\langle P_T(e_i e_j^\top), e_i e_j^\top\right\rangle\right|\le B_K
--   $$
--   for every coordinate, then the fixed matrix whose entries are
--   $$
--   E_{ij}\left\langle P_T(e_i e_j^\top),e_i e_j^\top\right\rangle^2
--   $$
--   has max-entry norm at most $B_E B_K^2$.
--
--   This node is purely formal algebra. Its role is to separate the Lean finite-supremum manipulation from the paper-backed A0 estimates used in the corrected rectangular all-equal bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (S : SVD M r)
    {signBound kernelBound : ℝ} :
    0 ≤ signBound →
    0 ≤ kernelBound →
    entrySupNorm (signMatrix S) ≤ signBound →
    (∀ i j, |tangentCoordinateKernel S i j i j| ≤ kernelBound) →
    entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      signBound * kernelBound ^ 2 := by
  sorry
