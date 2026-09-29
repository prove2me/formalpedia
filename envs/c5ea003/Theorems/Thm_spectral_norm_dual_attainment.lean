-- Prove2me | Theorems.Thm_spectral_norm_dual_attainment
-- name    : spectral_norm_dual_attainment
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:53:22.435211+00:00
-- url     : https://prove2.me/theorems/06fa187a-7c2c-41eb-b599-3165f38d2df2
-- statement:
--   **spectralNorm dual ATTAINMENT.** For every real matrix $X$ (viewed as the Euclidean linear map $\mathrm{toEuclideanLin}\,X$), there exist unit vectors $x,y$ ($\lVert x\rVert\le 1$, $\lVert y\rVert\le 1$) with $\langle Xx,\,y\rangle = \lVert X\rVert_{\mathrm{op}} = \mathrm{spectralNorm}\,X$. The operator norm of a finite-dimensional matrix is ATTAINED by a unit pair (extreme-value theorem: the unit ball of $\mathbb{R}^{n_2}$ is compact and $x\mapsto\lVert Xx\rVert$ is continuous, so the supremum defining the operator norm is achieved; the norming functional is then $y = Xx/\lVert Xx\rVert$). This is the ATTAINMENT companion to the previously-proved dual UPPER bound `spectral_norm_inner_pairing_bound` (d3228e1d, $\langle Xx,y\rangle\le\lVert X\rVert\,\lVert x\rVert\,\lVert y\rVert$); together they characterise the spectral norm by its dual pairing. This is the matrix→scalar norming-functional reduction used in de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) Proposition 1 / Lemma 2 to drop a Banach-valued tail to a scalar one.
-- source:
--   de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), Proposition 1 (Banach-valued norming functional); finite-dimensional operator-norm attainment via the extreme value theorem.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Order.Compact
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem spectral_norm_dual_attainment
    {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    ∃ (x : EuclideanSpace ℝ (Fin n2)) (y : EuclideanSpace ℝ (Fin n1)),
      ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      ⟪Matrix.toEuclideanLin X x, y⟫_ℝ = spectralNorm X := by sorry
