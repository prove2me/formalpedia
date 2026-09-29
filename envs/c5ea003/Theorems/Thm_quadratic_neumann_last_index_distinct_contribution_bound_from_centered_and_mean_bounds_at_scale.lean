-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- name    : quadratic_neumann_last_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:57:06.043416+00:00
-- url     : https://prove2.me/theorems/511067cd-48e9-4971-9602-03974cf75ac9
-- statement:
--   Purely formal bridge backed by Candes-Recht 2008, Section 6.3, PDF p. 33:
--   the `ω₁ = ω₂ ≠ ω₃` term is split using
--   `ξ_{ω₁}^2 = (1 - 2p)ξ_{ω₁} + p(1-p)`.
--
--   If the centered and mean pieces are bounded at a common scale, the original
--   last-index-distinct contribution is bounded at the sum of the constants times
--   that scale.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm
        (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm
        (quadraticNeumannLastIndexDistinctMeanContribution Omega S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by sorry
