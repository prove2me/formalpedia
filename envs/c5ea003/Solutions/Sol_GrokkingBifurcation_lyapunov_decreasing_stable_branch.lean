-- Prove2me | solution 1 for GrokkingBifurcation.lyapunov_decreasing_stable_branch
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:50:25.275971+00:00
-- url     : https://prove2.me/submissions/2163a4af-7c59-4b2d-a9db-0ed2f312e9c1

-- Sol generated from MachineLearning/GrokkingDelayedTransition/SaddleNodeLocal.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_SaddleNodeLocal

/-!
# Local saddle-node bifurcation theory for the grokking normal form

The catalog file `Catalog/MachineLearning/GrokkingPhaseTransition.lean` pairs a
delayed ReLU transition with the *algebraic* equilibrium structure of the
saddle-node normal form `μ - x²` (no equilibria / one / two).  This file supplies
the missing *analytic* layer, i.e. Future Direction 4 (local dynamical
bifurcation theory), Direction 5 (robustness) and Direction 6 (the connection to
a reduced loss landscape):

* `snField_hasDerivAt_state`, `snField_hasDerivAt_param`, `snField_secondDeriv`:
  the derivatives of the normal form;
* `saddleNode_nondegenerate`: the three classical saddle-node nondegeneracy
  conditions at the critical point `(μ, x) = (0, 0)`;
* `snField_deriv_stable_branch` / `snField_deriv_unstable_branch`: exchange of
  linear stability between the two branches;
* `lyapunov_decreasing_stable_branch` / `lyapunov_increasing_unstable_branch`:
  the *nonlinear* statement — along any solution of `x' = μ - x²` the squared
  distance to `√μ` strictly decreases, and the squared distance to `-√μ`
  strictly increases;
* `perturbed_two_equilibria`, `perturbed_zero_near_branch`,
  `perturbed_no_equilibrium`: the whole bifurcation diagram is robust: any
  continuous field uniformly `ε`-close to `μ - x²` still has two zeros for
  `μ > ε` (each within `O(ε)` of a branch) and none for `μ < -ε`;
* `reducedLoss_negGradient`, `reducedLoss_isLocalMin_stable_branch`,
  `reducedLoss_isLocalMax_unstable_branch`: the normal form is the negative
  gradient of the cubic reduced loss `x³/3 - μ x`, whose local minimum is the
  stable branch and whose local maximum is the unstable branch.
-/

open GrokkingBifurcation

open Real Set

/-! ### The normal form and its derivatives -/







/-! ### The two branches and exchange of stability -/





/-! ### Nonlinear (Lyapunov) stability along solutions -/

/-- Along any solution of `x' = μ - x²`, the squared distance to the upper
branch `√μ` has derivative `2 (x-√μ) (μ - x²)`; when `μ > 0` this equals
`-2 (x-√μ)² (x+√μ)`. -/
theorem lyapunov_stable_hasDerivAt (mu : ℝ) (x : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (snField mu (x t)) t) :
    HasDerivAt (fun s => (x s - Real.sqrt mu) ^ 2)
      (2 * (x t - Real.sqrt mu) * snField mu (x t)) t := by
  simpa using (hx.sub_const (Real.sqrt mu)).pow 2



/-! ### Robustness of the bifurcation diagram -/




/-! ### The reduced loss landscape (connection to an energy) -/









/-! ### The bottleneck delay: inverse-square-root scaling below the bifurcation

Third research cycle.  Just *below* the saddle-node (`μ < 0`) there is no
equilibrium, but the flow is slowed down dramatically near the ghost of the
vanished pair.  The Riccati equation `x' = μ - x²` has the explicit solution
`x(t) = -k tan(k t)` with `k = √(-μ)`, and the time needed to pass from `+A`
down to `-A` is `2 arctan(A/k)/k ≥ π/(2k) = (π/2)|μ|^{-1/2}`.  So the delay
diverges with exponent `1/2` in the bifurcation parameter — a different law
from the logarithmic divergence produced by weight decay in
`GradientFlowThreshold.lean`.
-/











open GrokkingBifurcation in
theorem solution(mu : ℝ) (hmu : 0 < mu) (x : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (snField mu (x t)) t)
    (hgt : -Real.sqrt mu < x t) (hne : x t ≠ Real.sqrt mu) :
    deriv (fun s => (x s - Real.sqrt mu) ^ 2) t < 0 := by
  have hsq : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt hmu.le
  rw [(lyapunov_stable_hasDerivAt mu x t hx).deriv]
  have h1 : 0 < (x t - Real.sqrt mu) ^ 2 := by
    have h : x t - Real.sqrt mu ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have h2 : 0 < x t + Real.sqrt mu := by linarith
  have hkey : 2 * (x t - Real.sqrt mu) * snField mu (x t)
      = -(2 * (x t - Real.sqrt mu) ^ 2 * (x t + Real.sqrt mu)) := by
    simp only [snField]; linear_combination (-(2 * (x t - Real.sqrt mu))) * hsq
  rw [hkey]
  nlinarith
