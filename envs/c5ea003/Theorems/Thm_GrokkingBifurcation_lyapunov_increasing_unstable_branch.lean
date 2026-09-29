-- Prove2me | Theorems.Thm_GrokkingBifurcation_lyapunov_increasing_unstable_branch
-- name    : GrokkingBifurcation.lyapunov_increasing_unstable_branch
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:32:56.465116+00:00
-- url     : https://prove2.me/theorems/dd61ef6e-8f5e-467a-99e4-2fa4d354e6bf
-- title:
--   Nonlinear instability of the lower branch.
-- statement:
--   **Nonlinear instability of the lower branch.**  For any solution of
--   `x' = μ - x²` strictly below the stable branch `√μ` and not sitting on the
--   unstable branch, the squared distance to `-√μ` is strictly increasing.
--
--   ```lean
--   theorem GrokkingBifurcation.lyapunov_increasing_unstable_branch(mu : ℝ) (hmu : 0 < mu) (x : ℝ → ℝ) (t : ℝ)
--       (hx : HasDerivAt x (snField mu (x t)) t)
--       (hlt : x t < Real.sqrt mu) (hne : x t ≠ -Real.sqrt mu) :
--       0 < deriv (fun s => (x s + Real.sqrt mu) ^ 2) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/SaddleNodeLocal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/SaddleNodeLocal.lean#L142

-- Thm stub generated from MachineLearning/GrokkingDelayedTransition/SaddleNodeLocal.lean
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

theorem GrokkingBifurcation.lyapunov_increasing_unstable_branch(mu : ℝ) (hmu : 0 < mu) (x : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (snField mu (x t)) t)
    (hlt : x t < Real.sqrt mu) (hne : x t ≠ -Real.sqrt mu) :
    0 < deriv (fun s => (x s + Real.sqrt mu) ^ 2) t := by sorry
