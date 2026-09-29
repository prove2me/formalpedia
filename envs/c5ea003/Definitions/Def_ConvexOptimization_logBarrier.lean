-- Prove2me | Definitions.Def_ConvexOptimization_logBarrier
-- name    : ConvexOptimization_logBarrier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T16:11:55.233068+00:00
-- url     : https://prove2.me/theorems/1726e20d-31cb-42ca-8fa7-0d34c1c51ff4
-- title:
--   Logarithmic barrier
-- statement:
--   The **logarithmic barrier** of a system of inequality constraints.
--
--   For constraint functions $f_1,\dots,f_m : \mathbb{R}^n \to \mathbb{R}$,
--
--   $$\varphi(x) \;=\; -\sum_{i=1}^{m} \log\bigl(-f_i(x)\bigr),$$
--
--   defined on the strictly feasible set $\{x : f_i(x) < 0 \text{ for all } i\}$, where every argument $-f_i(x)$ is positive.
--
--   The barrier is finite on the strict interior and blows up as any constraint approaches equality, so adding it to a scaled objective, $t f_0 + \varphi$, converts a constrained problem into an unconstrained one whose solution is pushed toward the interior. The family of minimizers as $t$ increases traces the *central path*, and its distance from optimality is exactly $m/t$ — the identity that drives the whole complexity analysis.
--
--   **Formalization Note** The definition is total: outside the strictly feasible set, $\log$ of a nonpositive argument takes Mathlib's junk value $0$, so every statement about the barrier carries an explicit strict-feasibility hypothesis and none relies on the values there. Source: B&V §11.2.1, p. 563.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 563, §11.2.1 eq. (11.5) (the logarithmic barrier function phi(x) = -sum_i log(-f_i(x)))

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- The logarithmic barrier `φ(x) = −Σ log(−fᵢ(x))` (B&V §11.2.1). -/
noncomputable def logBarrier {n mI : ℕ}
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -∑ i, Real.log (-(fc i x))

end ConvexOptimization


