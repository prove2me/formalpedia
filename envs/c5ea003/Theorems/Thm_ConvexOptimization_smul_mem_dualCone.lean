-- Prove2me | Theorems.Thm_ConvexOptimization_smul_mem_dualCone
-- name    : ConvexOptimization.smul_mem_dualCone
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-08-15T04:46:10.340309+00:00
-- url     : https://prove2.me/theorems/105068e7-d690-4926-bbb2-7a07eca2c666
-- title:
--   The dual cone is closed under nonnegative scaling
-- statement:
--   For a set $K \subseteq \mathbb{R}^d$ the dual cone is
--
--   $$K^{*} = \{\, y : \langle x, y\rangle \ge 0 \ \text{ for every } x \in K \,\}.$$
--
--   As the name indicates, $K^{*}$ is a cone and is always convex, whatever $K$ is. This statement is the scaling half of that assertion: if $z \in K^{*}$ and $c \ge 0$, then
--
--   $$c\, z \in K^{*}.$$
--
--   The verification is immediate from bilinearity of the inner product, $\langle x, c z\rangle = c \langle x, z\rangle \ge 0$, both factors being nonnegative. No hypothesis on $K$ is used — it need be neither convex nor a cone nor closed.
--
--   The result is what licenses renormalising a dual certificate, for example dividing a separating functional by the positive multiplier attached to the objective in order to obtain a Lagrange multiplier proper.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 51-53, §2.6.1, eq. (2.19) (dual cone) and the dual-cone property list

import Mathlib
import Definitions.Def_dualCone

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.smul_mem_dualCone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (c : ℝ) (hc : 0 ≤ c) :
    c • z ∈ dualCone K := by sorry
