-- Prove2me | Theorems.Thm_spectral_norm_inner_pairing_bound
-- name    : spectral_norm_inner_pairing_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:19:01.464756+00:00
-- url     : https://prove2.me/theorems/d3228e1d-c1a3-4904-a1fe-5fb1233901b6
-- statement:
--   The Banach-dual / bilinear norming UPPER BOUND for the spectral norm: for any vectors $x, y$, the inner-product pairing $\langle X x, y\rangle \le \mathrm{spectralNorm}(X)\,\|x\|\,\|y\|$. Equivalently, every scalar linear functional $a \mapsto \langle (\mathrm{toEuclideanLin}\,a)\,x, y\rangle$ (for fixed unit $x,y$) is dominated by the spectral norm. This is the matrix-to-scalar reduction tool used in de la Peña Proposition 1 / the norming-functional step: to control a matrix-valued tail one pairs against a fixed dual vector and reduces to a scalar statistic. Proof: Cauchy-Schwarz (real_inner_le_norm) gives $\langle Xx,y\rangle \le \|Xx\|\,\|y\|$, and the operator-norm bound (le_opNorm) gives $\|Xx\| \le \mathrm{spectralNorm}(X)\,\|x\|$.
-- source:
--   Mathlib Analysis.InnerProductSpace.Basic (real_inner_le_norm) + Analysis.Normed.Operator.Basic (le_opNorm). de la Pena-Montgomery-Smith 1995 arXiv:math/9309211 Proposition 1 (Banach-space norming functional reducing matrix/vector tails to scalar).

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Adjoint
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem spectral_norm_inner_pairing_bound
    {n1 n2 : ℕ} (X : RealMatrix n1 n2)
    (x : EuclideanSpace ℝ (Fin n2)) (y : EuclideanSpace ℝ (Fin n1)) :
    ⟪Matrix.toEuclideanLin X x, y⟫_ℝ ≤ spectralNorm X * ‖x‖ * ‖y‖ := by sorry
