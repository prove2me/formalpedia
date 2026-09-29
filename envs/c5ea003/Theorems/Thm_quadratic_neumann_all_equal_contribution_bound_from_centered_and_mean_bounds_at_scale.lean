-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_contribution_bound_from_centered_and_mean_bounds_at_scale
-- name    : quadratic_neumann_all_equal_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T17:17:55.681039+00:00
-- url     : https://prove2.me/theorems/d0b77a60-15cc-45e7-994b-d112ab763beb
-- statement:
--   This is the formal recombination of the two pieces in Candes-Recht equation (6.21).
--
--   Source location: Candes-Recht 2008, Section 6.3, PDF p. 30, equation (6.21). If the centered piece and deterministic mean piece from
--   $$
--   \xi_\omega^3=(1-3p+3p^2)\xi_\omega+p(1-3p+2p^2)
--   $$
--   are bounded by $C_{cent}\Phi$ and $C_{mean}\Phi$, then the original all-equal contribution is bounded by $(C_{cent}+C_{mean})\Phi$. This is purely the triangle inequality and the formal identity encoded by the project definitions.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_contribution_bound_from_centered_and_mean_bounds_at_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by
  sorry
