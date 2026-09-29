-- Prove2me | Theorems.Thm_SplitGeometry_jacobiEll_solves
-- name    : SplitGeometry.jacobiEll_solves
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:32.410626+00:00
-- url     : https://prove2.me/theorems/e9c9eba9-9d9b-4f31-9715-01dbb4631c89
-- title:
--   JacobiEll solves
-- statement:
--   Formal statement of `SplitGeometry.jacobiEll_solves` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SplitGeometry.jacobiEll_solves(k : ℝ) (t : ℝ) :
--       deriv (deriv (jacobiEll k)) t = -k * jacobiEll k t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Deviation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Deviation.lean#L70

-- Thm stub generated from Novelty/Deviation.lean
import Mathlib
import Definitions.Def_Novelty_Deviation

/-!
# Geodesic deviation: hyperbolic divergence vs. elliptic convergence

The separation `J(t)` between infinitesimally close geodesics obeys the **Jacobi
equation** `J'' + K · J = 0`, where `K` is the Gaussian curvature along the reference
geodesic.  The sign of `K` dictates the qualitative behaviour, and this is where the
exponential factors `e^{±t}` of the problem statement genuinely live.

This file records the two model behaviours in the constant-curvature normal form.

* **Negative curvature `K = -k < 0` (hyperbolic).**  `J(t) = sinh(√k · t)` solves
  `J'' + K J = J'' - k J = 0` and diverges: `J(t) → ∞`.  Nearby geodesics separate
  exponentially.  This is realised along the **x-axis**, where
  `K(x, 0) = -tanh² x ≤ 0` (see `Curvature.lean`).
* **Positive curvature `K = +k > 0` (elliptic).**  `J(t) = sin(√k · t)` solves
  `J'' + K J = J'' + k J = 0`, stays bounded (`|J| ≤ 1`) and refocuses: it returns to
  `0` at `t = π/√k`.  Nearby geodesics reconverge.

These are the standard Jacobi-field normal forms; combined with the curvature signs of
`Curvature.lean` they give the divergence statement for the x-axis.  (For this
particular metric the curvature is nonpositive everywhere along the axes, so the
elliptic case is not realised by the metric itself; the elliptic lemmas below describe
the generic `K > 0` behaviour.)
-/

open SplitGeometry

open Real Filter Topology



/-
**Hyperbolic case solves the Jacobi equation** `J'' - k J = 0`, i.e.
`J'' + K J = 0` with `K = -k`.
-/

/-
**Hyperbolic divergence.**  For negative curvature (`k > 0`) the Jacobi field grows
without bound: nearby geodesics separate.
-/

/-
**Elliptic case solves the Jacobi equation** `J'' + k J = 0`, i.e.
`J'' + K J = 0` with `K = +k`.
-/

theorem SplitGeometry.jacobiEll_solves(k : ℝ) (t : ℝ) :
    deriv (deriv (jacobiEll k)) t = -k * jacobiEll k t := by sorry
