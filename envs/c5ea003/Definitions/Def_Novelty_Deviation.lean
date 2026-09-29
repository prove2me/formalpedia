-- Prove2me | Definitions.Def_Novelty_Deviation
-- name    : Novelty_Deviation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:03.906008+00:00
-- url     : https://prove2.me/theorems/f8c63373-51dd-4947-a8da-05ec05463f0f
-- title:
--   Aether Catalog definitions — Novelty_Deviation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Deviation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Deviation.lean by skeleton subtraction
import Mathlib

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

namespace SplitGeometry

open Real Filter Topology

/-- Hyperbolic Jacobi field `J(t) = sinh(√k · t)` for curvature `K = -k`. -/
noncomputable def jacobiHyp (k t : ℝ) : ℝ := Real.sinh (Real.sqrt k * t)

/-- Elliptic Jacobi field `J(t) = sin(√k · t)` for curvature `K = +k`. -/
noncomputable def jacobiEll (k t : ℝ) : ℝ := Real.sin (Real.sqrt k * t)

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

/-
**Elliptic boundedness.**  For positive curvature the Jacobi field stays bounded.
-/

/-
**Elliptic refocusing.**  For positive curvature (`k > 0`) the Jacobi field returns
to zero at `t = π/√k`: nearby geodesics reconverge.
-/

end SplitGeometry


