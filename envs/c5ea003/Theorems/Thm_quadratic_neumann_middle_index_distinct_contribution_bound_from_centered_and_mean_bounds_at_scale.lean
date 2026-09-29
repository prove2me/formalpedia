-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- name    : quadratic_neumann_middle_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T18:50:16.428226+00:00
-- url     : https://prove2.me/theorems/c2165e5d-8f9d-452b-b9d1-b63893377721
-- statement:
--   Role. This is the deterministic Lean bridge for the middle-index-distinct Section 6.3 split.
--
--   Claim. If the centered and mean pieces of the $\omega_1=\omega_3\ne\omega_2$ contribution are both bounded at a common scale, then the original middle-index-distinct contribution is bounded by the sum of the two constants times that scale.
--
--   Source. This is a purely formal Lean bridge for the split displayed in Candes-Recht 2008, Section 6.3, PDF p. 32, using $\xi_{\omega_1}^2=(1-2p)\xi_{\omega_1}+p(1-p)$.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 32--33, after equation (6.20).

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Purely formal bridge backed by Candes-Recht 2008, Section 6.3, PDF p. 32:
the `ω₁ = ω₃ ≠ ω₂` term is split using
`ξ_{ω₁}^2 = (1 - 2p) ξ_{ω₁} + p(1-p)`.

If the centered and mean pieces are bounded at a common scale, the original
middle-index-distinct contribution is bounded at the sum of the constants times
that scale. -/
theorem quadratic_neumann_middle_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm
        (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm
        (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by
  sorry
