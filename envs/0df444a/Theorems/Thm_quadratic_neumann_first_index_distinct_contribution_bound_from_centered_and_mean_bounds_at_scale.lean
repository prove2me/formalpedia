-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- name    : quadratic_neumann_first_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T17:27:13.970035+00:00
-- url     : https://prove2.me/theorems/44ab4595-0947-4071-9196-b307b3c7d3c5
-- statement:
--   This is the formal recombination of the two terms in the Candes-Recht $\omega_1\ne\omega_2=\omega_3$ case.
--
--   Source location: Candes-Recht 2008, Section 6.3, PDF pp. 31--32. The identity
--   $$
--   (\xi_{\omega_2})^2=(1-2p)\xi_{\omega_2}+p(1-p)
--   $$
--   splits the case into centered and mean/coefficient contributions. If those two pieces are bounded by $C_{cent}\Phi$ and $C_{mean}\Phi$, then the original contribution is bounded by $(C_{cent}+C_{mean})\Phi$. This node is the formal triangle-inequality bridge.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm
        (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm
        (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by
  sorry
