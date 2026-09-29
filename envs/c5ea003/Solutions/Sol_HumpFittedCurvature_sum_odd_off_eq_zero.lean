-- Prove2me | solution 1 for HumpFittedCurvature.sum_odd_off_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:46:44.041967+00:00
-- url     : https://prove2.me/submissions/f0574e9b-9993-41a6-8b21-fd34a053c579

-- Sol generated from Algebra/HumpFittedCurvature.lean
import Mathlib
import Definitions.Def_Algebra_HumpFittedCurvature
import Definitions.Def_Algebra_HumpWindowGeometry
/-
# The fitted quadratic coefficient is a certificate of concavity

Second formal core of experiment **581** (paper 231).  The experiment's central
descriptive statistic is the **quadratic-fit curvature** `c` of the binned ratio
profile `R = T/M`: `c = -0.105` pooled controls, `c = -0.299` dominant band,
`c = -0.18 / -0.25 / -0.44` in the three LPF terciles, `c = -0.13` in the first
`k100` tercile.  The verdict language ("concave in ALL THREE") reads a negative
fitted `c` as *concavity of the underlying profile*.

That reading is not automatic: `c` is an inner product of the profile against a
grid-dependent orthogonal quadratic, and one has to know that this inner product
cannot be negative for an accident of the grid.  This file proves it, in the
exact discrete form used by the pipeline (finitely many equal-width bins).

## Main results

* `HumpFittedCurvature.sum_profile_mul_quadratic_nonpos` — **sign theorem**: for
  any concave profile `g`, any finite grid, and any quadratic
  `q(y) = (y-r₁)(y-r₂)` that is orthogonal to constants and to the identity on
  that grid, `∑ g(tᵢ) q(tᵢ) ≤ 0`.  The proof subtracts the chord of `g` through
  the two roots of `q`; orthogonality kills the chord, and the residual has the
  opposite sign to `q` at every single grid point.
* `HumpFittedCurvature.sum_profile_mul_quadratic_neg` — strict version for
  strictly concave profiles.
* `HumpFittedCurvature.affine_profile_sum_eq_zero` — the **control**:
  an affine profile fits with curvature exactly `0`, matching the experiment's
  "controls clean everywhere".
* `HumpFittedCurvature.binGrid_orth_const`, `binGrid_orth_id` — the equal-width
  bin grid of the pipeline, with the explicit orthogonal quadratic
  `q(y) = (y-m)² - h²·V(n)`, is orthogonal to constants and to the identity for
  **every** bin width `h` and **every** grid centre `m`.
* `HumpFittedCurvature.fitCurvature_neg_binGrid` — hence for any strictly
  concave profile the measured curvature is strictly negative.
* `HumpFittedCurvature.window_fitCurvature_neg` — applied to the `j² − N`
  log-size profile of `Algebra.HumpWindowGeometry`: **the geometric channel `H0`
  predicts a strictly negative fitted curvature, for every bin width and every
  grid offset.**  This is exactly the pre-registered "bin-width permutation /
  u-grid shift" probe, and `H0` passes it: the concavity sign is invariant.

Together with `HumpWindowGeometry.vertex_lt_midpoint` this sharpens the verdict:
the geometry predicts the *sign* robustly but cannot place the *vertex*.
-/

open HumpFittedCurvature

open Finset Set HumpWindowGeometry

/-! ## 1. The fitted curvature statistic -/


/-! ## 2. Concave profiles versus the chord through the roots -/

variable {S : Set ℝ} {g : ℝ → ℝ} {r₁ r₂ : ℝ}








/-! ## 3. The sign theorem -/








/-! ## 4. The equal-width bin grid of the pipeline -/















/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/






open HumpFittedCurvature in
theorem solution(n : ℕ) {F : ℝ → ℝ} (hF : ∀ y : ℝ, F (-y) = -F y) :
    ∑ i ∈ range n, F (off n i) = 0 := by
  have hrefl : ∑ i ∈ range n, F (off n (n - 1 - i)) = ∑ i ∈ range n, F (off n i) :=
    Finset.sum_range_reflect (fun i => F (off n i)) n
  have hneg : ∀ i ∈ range n, F (off n (n - 1 - i)) = -F (off n i) := by
    intro i hi
    have hi' : i < n := mem_range.1 hi
    have hcast : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
      have h' : (n - 1 - i : ℕ) = n - (1 + i) := by omega
      have hle : 1 + i ≤ n := by omega
      rw [h', Nat.cast_sub hle]
      push_cast
      ring
    have hoff : off n (n - 1 - i) = -(off n i) := by
      rw [off, off, hcast]; ring
    rw [hoff, hF]
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib] at hrefl
  linarith
