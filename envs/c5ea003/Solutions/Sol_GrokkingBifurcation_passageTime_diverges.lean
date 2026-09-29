-- Prove2me | solution 1 for GrokkingBifurcation.passageTime_diverges
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:50:26.368491+00:00
-- url     : https://prove2.me/submissions/31cf36b4-849d-4ca0-adf5-b4fddba74160

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







/-- **Inverse-square-root bottleneck bound.**  Whenever the observation level `A`
is at least `k = √(-μ)`, the passage time is at least `π/(2k)`. -/
theorem passageTime_lower_bound (k A : ℝ) (hk : 0 < k) (hkA : k ≤ A) :
    Real.pi / (2 * k) ≤ passageTime k A := by
  have h1 : (1 : ℝ) ≤ A / k := (one_le_div hk).mpr hkA
  have h2 : Real.pi / 4 ≤ Real.arctan (A / k) := by
    have := Real.arctan_mono h1
    rwa [Real.arctan_one] at this
  simp only [passageTime]
  rw [div_le_div_iff₀ (by positivity) hk]
  nlinarith [Real.pi_pos]




open GrokkingBifurcation in
theorem solution(A : ℝ) (hA : 0 < A) (T : ℝ) :
    ∃ k : ℝ, 0 < k ∧ k ≤ A ∧ T < passageTime k A := by
  have hpi := Real.pi_pos
  set k : ℝ := min A (Real.pi / (2 * (|T| + 1))) with hk
  have hTpos : 0 < |T| + 1 := by positivity
  have hkpos : 0 < k := lt_min hA (by positivity)
  have hkA : k ≤ A := min_le_left _ _
  refine ⟨k, hkpos, hkA, lt_of_lt_of_le ?_ (passageTime_lower_bound k A hkpos hkA)⟩
  have hk2 : k ≤ Real.pi / (2 * (|T| + 1)) := min_le_right _ _
  have hle : |T| + 1 ≤ Real.pi / (2 * k) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hk2
    nlinarith
  have := le_abs_self T
  linarith
