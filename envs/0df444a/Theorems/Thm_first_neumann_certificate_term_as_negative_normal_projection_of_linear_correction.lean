-- Prove2me | Theorems.Thm_first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction
-- name    : first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T05:14:09.155504+00:00
-- url     : https://prove2.me/theorems/a1f2e567-d23f-496b-94fc-e84fbc94e671
-- statement:
--   This is the corrected algebraic identification of the first Neumann certificate term under the local Lean convention
--   $$
--   H=P_T-p^{-1}P_TP_\Omega P_T.
--   $$
--   With this sign convention, the first certificate term is
--   $$
--   p^{-1}P_{T^\perp}P_\Omega P_T H(E)
--   =-P_{T^\perp}(S_0+S_1),
--   $$
--   where $S_0$ and $S_1$ are the diagonal and off-diagonal pieces of the unprojected centered correction in equation (6.8).
--
--   Source: Candes-Recht 2008, PDF p. 26, Section 6.2, the display defining $S=p^{-1}(P_\Omega-pI)H(E)$ and equation (6.8).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact Matrix Completion via Convex Optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    neumannCertificateTerm Omega S p 1 =
      -normalProjection S
        (linearNeumannDiagonalContribution Omega S p +
          linearNeumannOffDiagonalContribution Omega S p) := by
  sorry
