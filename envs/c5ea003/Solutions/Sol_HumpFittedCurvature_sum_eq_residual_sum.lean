-- Prove2me | solution 1 for HumpFittedCurvature.sum_eq_residual_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:51:20.074234+00:00
-- url     : https://prove2.me/submissions/84527300-54e1-4dc4-a2c1-b100375c92c5

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



/-- The chord through the two roots is affine, hence orthogonal to `q`. -/
theorem chord_is_affine (g : ℝ → ℝ) {r₁ r₂ : ℝ} (hr : r₁ < r₂) :
    ∀ y : ℝ, chord g r₁ r₂ y
      = (g r₁ - r₁ * ((g r₂ - g r₁) / (r₂ - r₁))) + ((g r₂ - g r₁) / (r₂ - r₁)) * y := by
  intro y
  have hne : r₂ - r₁ ≠ 0 := (sub_pos.2 hr).ne'
  rw [chord]
  field_simp
  ring

/-- **Control.**  An affine profile has zero inner product with `q`. -/
theorem affine_profile_sum_eq_zero (u v : ℝ) {n : ℕ} {t : ℕ → ℝ} {r₁ r₂ : ℝ}
    (hq0 : ∑ i ∈ range n, ((t i - r₁) * (t i - r₂)) = 0)
    (hq1 : ∑ i ∈ range n, t i * ((t i - r₁) * (t i - r₂)) = 0) :
    ∑ i ∈ range n, (u + v * t i) * ((t i - r₁) * (t i - r₂)) = 0 := by
  have hterm : ∀ i ∈ range n, (u + v * t i) * ((t i - r₁) * (t i - r₂))
      = u * ((t i - r₁) * (t i - r₂)) + v * (t i * ((t i - r₁) * (t i - r₂))) := by
    intro i _; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hq0, hq1]
  ring




/-! ## 4. The equal-width bin grid of the pipeline -/















/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/






open HumpFittedCurvature in
theorem solution(g : ℝ → ℝ) {r₁ r₂ : ℝ} (hr : r₁ < r₂) {n : ℕ} {t : ℕ → ℝ}
    (hq0 : ∑ i ∈ range n, ((t i - r₁) * (t i - r₂)) = 0)
    (hq1 : ∑ i ∈ range n, t i * ((t i - r₁) * (t i - r₂)) = 0) :
    ∑ i ∈ range n, g (t i) * ((t i - r₁) * (t i - r₂))
      = ∑ i ∈ range n, (g (t i) - chord g r₁ r₂ (t i)) * ((t i - r₁) * (t i - r₂)) := by
  have hchordsum : ∑ i ∈ range n, chord g r₁ r₂ (t i) * ((t i - r₁) * (t i - r₂)) = 0 := by
    have hterm : ∀ i ∈ range n, chord g r₁ r₂ (t i) * ((t i - r₁) * (t i - r₂))
        = ((g r₁ - r₁ * ((g r₂ - g r₁) / (r₂ - r₁)))
            + ((g r₂ - g r₁) / (r₂ - r₁)) * t i) * ((t i - r₁) * (t i - r₂)) := by
      intro i _; rw [chord_is_affine g hr]
    rw [Finset.sum_congr rfl hterm]
    exact affine_profile_sum_eq_zero _ _ hq0 hq1
  have hterm : ∀ i ∈ range n, g (t i) * ((t i - r₁) * (t i - r₂))
      = (g (t i) - chord g r₁ r₂ (t i)) * ((t i - r₁) * (t i - r₂))
        + chord g r₁ r₂ (t i) * ((t i - r₁) * (t i - r₂)) := by
    intro i _; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hchordsum, add_zero]
