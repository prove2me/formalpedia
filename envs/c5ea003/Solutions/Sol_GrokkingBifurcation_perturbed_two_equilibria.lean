-- Prove2me | solution 1 for GrokkingBifurcation.perturbed_two_equilibria
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:50:26.872866+00:00
-- url     : https://prove2.me/submissions/df330c40-1fad-4318-9190-7d8c7c0602c0

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











open GrokkingBifurcation in
theorem solution(mu eps : ℝ) (heps : 0 < eps) (hlt : eps < mu)
    (g : ℝ → ℝ) (hg : Continuous g) (hclose : ∀ x, |g x - snField mu x| ≤ eps) :
    ∃ x₁ x₂ : ℝ, x₁ < 0 ∧ 0 < x₂ ∧ g x₁ = 0 ∧ g x₂ = 0 := by
  have hmu : 0 < mu := heps.trans hlt
  set b : ℝ := Real.sqrt (mu + 2 * eps) with hb
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hbsq : b ^ 2 = mu + 2 * eps := Real.sq_sqrt (by linarith)
  have hzero : 0 < g 0 := by
    have h := abs_le.mp (hclose 0)
    simp only [snField] at h
    linarith [h.1]
  have hpos : g b < 0 := by
    have h := abs_le.mp (hclose b)
    simp only [snField] at h
    have h2 := h.2
    rw [hbsq] at h2
    linarith
  have hneg : g (-b) < 0 := by
    have h := abs_le.mp (hclose (-b))
    simp only [snField] at h
    have h2 := h.2
    rw [show (-b) ^ 2 = b ^ 2 by ring, hbsq] at h2
    linarith
  obtain ⟨x₂, hx₂mem, hx₂⟩ : (0 : ℝ) ∈ g '' (Ioo 0 b) :=
    intermediate_value_Ioo' (le_of_lt hbpos) hg.continuousOn ⟨hpos, hzero⟩
  obtain ⟨x₁, hx₁mem, hx₁⟩ : (0 : ℝ) ∈ g '' (Ioo (-b) 0) :=
    intermediate_value_Ioo (by linarith : (-b : ℝ) ≤ 0) hg.continuousOn ⟨hneg, hzero⟩
  exact ⟨x₁, x₂, hx₁mem.2, hx₂mem.1, hx₁, hx₂⟩
