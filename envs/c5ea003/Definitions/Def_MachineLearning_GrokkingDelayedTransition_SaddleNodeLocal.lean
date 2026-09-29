-- Prove2me | Definitions.Def_MachineLearning_GrokkingDelayedTransition_SaddleNodeLocal
-- name    : MachineLearning_GrokkingDelayedTransition_SaddleNodeLocal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:37.762982+00:00
-- url     : https://prove2.me/theorems/68e48894-aeed-4d8e-99ad-4c8adbaef2f4
-- title:
--   Aether Catalog definitions — MachineLearning_GrokkingDelayedTransition_SaddleNodeLocal
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GrokkingDelayedTransition.SaddleNodeLocal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GrokkingDelayedTransition/SaddleNodeLocal.lean by skeleton subtraction
import Mathlib

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

namespace GrokkingBifurcation

open Real Set

/-! ### The normal form and its derivatives -/

/-- The one-dimensional saddle-node vector field `x ↦ μ - x²`. -/
def snField (mu x : ℝ) : ℝ := mu - x ^ 2






/-! ### The two branches and exchange of stability -/





/-! ### Nonlinear (Lyapunov) stability along solutions -/




/-! ### Robustness of the bifurcation diagram -/




/-! ### The reduced loss landscape (connection to an energy) -/

/-- The reduced (cubic) loss landscape whose negative gradient is the
saddle-node normal form. -/
noncomputable def reducedLoss (mu x : ℝ) : ℝ := x ^ 3 / 3 - mu * x








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

/-- Explicit solution of `x' = μ - x²` for `μ = -k² < 0`. -/
noncomputable def snBottleneck (k t : ℝ) : ℝ := -k * Real.tan (k * t)





/-- The time the solution spends crossing the bottleneck from `+A` to `-A`. -/
noncomputable def passageTime (k A : ℝ) : ℝ := 2 * Real.arctan (A / k) / k




end GrokkingBifurcation


