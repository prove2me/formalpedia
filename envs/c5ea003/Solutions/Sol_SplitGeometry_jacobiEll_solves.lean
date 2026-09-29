-- Prove2me | solution 1 for SplitGeometry.jacobiEll_solves
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:29.802812+00:00
-- url     : https://prove2.me/submissions/8f57879c-9337-4131-97c3-33b35f437c2f

-- Sol generated from Novelty/Deviation.lean
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

/-
**Elliptic boundedness.**  For positive curvature the Jacobi field stays bounded.
-/

/-
**Elliptic refocusing.**  For positive curvature (`k > 0`) the Jacobi field returns
to zero at `t = π/√k`: nearby geodesics reconverge.
-/


open SplitGeometry in
theorem solution(k : ℝ) (t : ℝ) :
    deriv (deriv (jacobiEll k)) t = -k * jacobiEll k t := by
  have hd1 : deriv (jacobiEll k) = fun u => Real.cos (Real.sqrt k * u) * Real.sqrt k := by
    funext u
    simpa [jacobiEll] using (((hasDerivAt_id u).const_mul (Real.sqrt k)).sin).deriv
  have hd2 : deriv (deriv (jacobiEll k)) t
      = -Real.sin (Real.sqrt k * t) * Real.sqrt k * Real.sqrt k := by
    rw [hd1]
    simpa using (((hasDerivAt_id t).const_mul (Real.sqrt k)).cos.mul_const (Real.sqrt k)).deriv
  rw [hd2]
  simp only [jacobiEll]
  by_cases h : 0 ≤ k
  · rw [mul_assoc, Real.mul_self_sqrt h]; ring
  · rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp h).le]; simp
