-- Prove2me | solution 1 for HumpFittedCurvature.binGrid_orth_id
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:48:41.93551+00:00
-- url     : https://prove2.me/submissions/90b2d222-7ab7-4c09-976b-3638c135db63

-- Sol generated from Algebra/HumpFittedCurvature.lean
import Mathlib
import Definitions.Def_Algebra_HumpFittedCurvature
import Definitions.Def_Algebra_HumpWindowGeometry
import Theorems.Thm_HumpFittedCurvature_gridVar_pos
import Theorems.Thm_HumpFittedCurvature_sum_odd_off_eq_zero
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





theorem sum_off_eq_zero (n : ℕ) : ∑ i ∈ range n, off n i = 0 := by
  have h := sum_odd_off_eq_zero n (F := fun y : ℝ => y) (by intro y; ring)
  simpa using h

theorem sum_off_cube_eq_zero (n : ℕ) : ∑ i ∈ range n, (off n i) ^ 3 = 0 :=
  sum_odd_off_eq_zero n (F := fun y : ℝ => y ^ 3) (by intro y; ring)

theorem sum_off_sq (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ range n, (off n i) ^ 2 = n * gridVar n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [gridVar]
  field_simp




/-- The defining factorisation: the orthogonal quadratic of the bin grid. -/
theorem quadratic_factor {n : ℕ} (hn : 2 ≤ n) (m h y : ℝ) :
    (y - (m - rootHalf n h)) * (y - (m + rootHalf n h))
      = (y - m) ^ 2 - h ^ 2 * gridVar n := by
  have hsq : Real.sqrt (gridVar n) ^ 2 = gridVar n :=
    Real.sq_sqrt (le_of_lt (gridVar_pos hn))
  rw [rootHalf]
  nlinarith [hsq]




/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/






open HumpFittedCurvature in
theorem solution{n : ℕ} (hn : 2 ≤ n) (m h : ℝ) :
    ∑ i ∈ range n, binGrid n m h i * ((binGrid n m h i - (m - rootHalf n h))
      * (binGrid n m h i - (m + rootHalf n h))) = 0 := by
  have hn0 : 0 < n := by omega
  have hterm : ∀ i ∈ range n, binGrid n m h i * ((binGrid n m h i - (m - rootHalf n h))
      * (binGrid n m h i - (m + rootHalf n h)))
      = m * (h ^ 2 * ((off n i) ^ 2 - gridVar n))
        + h ^ 3 * ((off n i) ^ 3 - gridVar n * off n i) := by
    intro i _
    rw [quadratic_factor hn, binGrid]
    ring
  have hA : ∑ i ∈ range n, m * (h ^ 2 * ((off n i) ^ 2 - gridVar n)) = 0 := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_off_sq n hn0,
      Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  have hB : ∑ i ∈ range n, h ^ 3 * ((off n i) ^ 3 - gridVar n * off n i) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_off_cube_eq_zero, ← Finset.mul_sum,
      sum_off_eq_zero]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hA, hB]
  ring
