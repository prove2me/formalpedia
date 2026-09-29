-- Prove2me | Definitions.Def_Geometry_Convergence
-- name    : Geometry_Convergence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:54:06.261516+00:00
-- url     : https://prove2.me/theorems/09842227-578d-416d-8ac1-b6ef0151ea29
-- title:
--   Aether Catalog definitions — Geometry_Convergence
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Convergence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Convergence.lean by skeleton subtraction
import Mathlib
/-
  Natural Gradient Convergence on Dually Flat Manifolds: Theorems
  ===============================================================

  This file proves the core convergence theorems for natural gradient descent
  on dually flat manifolds (exponential families). The main results are:

  1. **Telescoping descent bound** (`telescope_descent_bound`):
     From a one-step Bregman descent inequality, derive a weighted sum bound
     on excess loss.

  2. **Free energy dissipation** (`bregman_nonincreasing`):
     Under a small-step condition, the Bregman Lyapunov energy is
     monotonically nonincreasing — a discrete entropy-production theorem.

  3. **O(H_t/t) convergence rate** (`convergence_harmonic_step`):
     With harmonic step sizes α_t = 1/(t+1), the excess loss satisfies
       t · e(t) ≤ B + A · H(t)
     where H(t) is the partial harmonic series. This is proved by induction.

  4. **Natural gradient ↔ mirror descent** (`naturalGrad_eq_mirrorDescent_dual`):
     Under the dually flat chain-rule identity, the natural gradient update
     in θ-coordinates corresponds to a gradient step in η-coordinates.

  5. **Bregman nonnegativity** (`bregmanDiv_nonneg_of_convex`):
     The Bregman divergence of a convex function is always nonnegative,
     connecting to `logPartition_convex`.

  These results build on `logPartition_convex`, `fisher_eq_sufficientStatCov`,
  and `fisherMatrix_posSemidef` from the information geometry catalog.
-/


open Finset BigOperators

noncomputable section

/-! ## Harmonic step and sum (local copies to avoid import issues) -/

/-- Harmonic step size: α_t = 1/(t+1). -/
def harmonicStep' (t : ℕ) : ℝ := 1 / ((t : ℝ) + 1)

/-- Harmonic sum: H(t) = ∑_{k=0}^{t-1} 1/(k+1). -/
def harmonicSum' : ℕ → ℝ
  | 0 => 0
  | t + 1 => harmonicSum' t + harmonicStep' t




/-! ## Theorem 1: Telescoping Descent Bound

From a one-step Bregman descent inequality
  D(t+1) ≤ D(t) - α(t) · e(t) + C · α(t)²
we derive a weighted sum bound:
  ∑_{k=0}^{T-1} α(k) · e(k) ≤ D(0) + C · ∑_{k=0}^{T-1} α(k)²
by telescoping. -/

/-
**Telescoping descent bound**: If a Lyapunov sequence satisfies a one-step
    descent inequality with excess loss and quadratic error, then the weighted
    sum of excess losses is bounded by the initial Lyapunov plus accumulated error.
    This is the fundamental telescope argument for mirror descent / natural gradient.
-/

/-! ## Theorem 2: Free Energy Dissipation

When the step size is small enough relative to the excess loss,
the Bregman divergence is monotonically nonincreasing.
This is a discrete analog of entropy production in statistical mechanics. -/

/-
**Free energy dissipation**: If the Bregman Lyapunov satisfies a descent
    inequality and the step size is small enough that C·α(t) ≤ e(t), then
    the Lyapunov energy decreases at every step.
-/

/-! ## Theorem 3: Convergence Rate with Harmonic Steps

The main convergence theorem: with harmonic step sizes α_t = 1/(t+1) and
a contraction-type descent recurrence, the excess loss decays as O(H_t/t). -/

/-
**Convergence rate with harmonic steps**: If the excess loss sequence
    satisfies the contraction recurrence
      e(t+1) ≤ (1 - 1/(t+1)) · e(t) + A/(t+1)²
    and e(0) ≤ B, then for all t ≥ 1:
      t · e(t) ≤ B + A · H(t)
    where H(t) = ∑_{k=1}^{t} 1/k is the harmonic sum. This gives
    a convergence rate of O((log t)/t) since H(t) ~ ln(t).
-/

/-! ## Theorem 4: Natural Gradient = Mirror Descent in Dual Coordinates

The natural gradient update in θ-coordinates, when translated to
expectation (dual) coordinates η = ∇ψ(θ), becomes a standard gradient
step in the dual space. This is stated as an identity under the chain
rule hypothesis that connects primal and dual gradients. -/

/-
**Natural gradient = mirror descent in dual coordinates**:
    If the natural gradient direction equals the dual gradient of the loss
    in expectation coordinates, and the expectation map linearizes the step,
    then the natural gradient update in η-coordinates is a plain gradient step.

    Precisely: η(θ - α·v) = η(θ) - α·I(θ)·v (first-order), and if
    v = I⁻¹·∇L = ∇ηL̃, then η(θ') = η(θ) - α·∇L(θ), which is
    exactly the mirror descent update.
-/

/-! ## Theorem 5: Bregman Divergence Nonnegativity

A fundamental property: the Bregman divergence of a function
satisfying a first-order convexity condition is always nonneg. -/

/-
The Bregman divergence is nonnegative when the generating function
    satisfies the first-order convexity condition:
      ψ(x) ≥ ψ(y) + ⟨∇ψ(y), x - y⟩ for all x, y.
    This connects directly to `logPartition_convex`.
-/

/-! ## Theorem 6: Weighted Average Convergence

From the telescoping bound, derive convergence of the weighted average
of loss values. -/

/-
**Weighted average convergence**: From the telescoping descent bound,
    the weighted average of excess losses is bounded.
-/

/-! ## Theorem 7: Harmonic Sum Squared Bound

The sum of squared harmonic steps is bounded. -/

/-
The partial sum of squared reciprocals is bounded:
    ∑_{k=0}^{T-1} 1/(k+1)² ≤ 2 for all T.
    This is a consequence of 1/(k+1)² ≤ 1/k - 1/(k+1) for k ≥ 1.
-/

end


