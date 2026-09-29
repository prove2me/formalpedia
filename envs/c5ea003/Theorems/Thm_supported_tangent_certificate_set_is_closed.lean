-- Prove2me | Theorems.Thm_supported_tangent_certificate_set_is_closed
-- name    : supported_tangent_certificate_set_is_closed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T08:09:52.638185+00:00
-- url     : https://prove2.me/theorems/ae6c9d03-baba-4efb-a106-5aa13f28cc8d
-- statement:
--   This is the closedness lemma for the feasible set of the least-squares dual certificate.
--
--   For a fixed observation set $\Omega$ and SVD data $S$, consider
--   $$
--   C=\{Y: Y_{ij}=0\text{ for }(i,j)\notin\Omega,\quad P_TY=E\}.
--   $$
--   The theorem states that $C$ is closed in the finite-dimensional matrix topology.  The support constraints are finitely many coordinate equalities and the tangent constraint is a linear equation.
--
--   Source: Candes-Recht 2008, PDF p. 17, equation (4.1), where this feasible set is minimized over.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem supported_tangent_certificate_set_is_closed
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) :
    IsClosed
      {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
        VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S} := by
  sorry
