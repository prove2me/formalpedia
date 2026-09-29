-- Prove2me | solution 1 for HumpFittedCurvature.residual_mul_quadratic_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:51:19.508569+00:00
-- url     : https://prove2.me/submissions/db3001aa-4c47-4cbd-bda6-ba8fd8d48a9b

-- Sol generated from Algebra/HumpFittedCurvature.lean
import Mathlib
import Definitions.Def_Algebra_HumpFittedCurvature
import Definitions.Def_Algebra_HumpWindowGeometry
import Theorems.Thm_HumpWindowGeometry_gap_nonneg_of_concaveOn
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

/-- **Bridge identity, right side.**  For `r₁ < r₂ < y` the deficit of a profile
below the `[r₁,r₂]`-chord at `y` is a positive multiple of its excess above the
`[r₁,y]`-chord at `r₂`.  (Pure algebra: both measure the same triangle.) -/
theorem chord_bridge_right (g : ℝ → ℝ) {r₁ r₂ y : ℝ} (h12 : r₁ < r₂) (h2y : r₂ < y) :
    chord g r₁ r₂ y - g y = (y - r₁) / (r₂ - r₁) * gap g r₁ y r₂ := by
  have hne1 : r₂ - r₁ ≠ 0 := (sub_pos.2 h12).ne'
  have hne2 : y - r₁ ≠ 0 := (sub_pos.2 (lt_trans h12 h2y)).ne'
  rw [gap, chord, chord]
  field_simp
  ring

/-- **Bridge identity, left side.**  For `y < r₁ < r₂`. -/
theorem chord_bridge_left (g : ℝ → ℝ) {r₁ r₂ y : ℝ} (h12 : r₁ < r₂) (hy1 : y < r₁) :
    chord g r₁ r₂ y - g y = (r₂ - y) / (r₂ - r₁) * gap g y r₂ r₁ := by
  have hne1 : r₂ - r₁ ≠ 0 := (sub_pos.2 h12).ne'
  have hne2 : r₂ - y ≠ 0 := (sub_pos.2 (lt_trans hy1 h12)).ne'
  rw [gap, chord, chord]
  field_simp
  ring

/-- Between the two roots, a concave profile is above the chord. -/
theorem chord_le_of_mem_Icc (hg : ConcaveOn ℝ S g) (h1 : r₁ ∈ S) (h2 : r₂ ∈ S) (hr : r₁ < r₂)
    {y : ℝ} (hy : y ∈ Icc r₁ r₂) : chord g r₁ r₂ y ≤ g y := by
  have := gap_nonneg_of_concaveOn hg h1 h2 hr hy.1 hy.2
  rw [gap] at this
  linarith

/-- Beyond the right root, a concave profile is below the chord. -/
theorem le_chord_of_gt (hg : ConcaveOn ℝ S g) (h1 : r₁ ∈ S) (hr : r₁ < r₂)
    {y : ℝ} (hyS : y ∈ S) (hy : r₂ < y) : g y ≤ chord g r₁ r₂ y := by
  have hgap : 0 ≤ gap g r₁ y r₂ :=
    gap_nonneg_of_concaveOn hg h1 hyS (lt_trans hr hy) (le_of_lt hr) (le_of_lt hy)
  have hcoef : 0 < (y - r₁) / (r₂ - r₁) := div_pos (by linarith) (by linarith)
  have := chord_bridge_right g hr hy
  nlinarith [mul_nonneg (le_of_lt hcoef) hgap]


/-- Before the left root, a concave profile is below the chord. -/
theorem le_chord_of_lt (hg : ConcaveOn ℝ S g) (h2 : r₂ ∈ S) (hr : r₁ < r₂)
    {y : ℝ} (hyS : y ∈ S) (hy : y < r₁) : g y ≤ chord g r₁ r₂ y := by
  have hgap : 0 ≤ gap g y r₂ r₁ :=
    gap_nonneg_of_concaveOn hg hyS h2 (lt_trans hy hr) (le_of_lt hy) (le_of_lt hr)
  have hcoef : 0 < (r₂ - y) / (r₂ - r₁) := div_pos (by linarith) (by linarith)
  have := chord_bridge_left g hr hy
  nlinarith [mul_nonneg (le_of_lt hcoef) hgap]


/-! ## 3. The sign theorem -/








/-! ## 4. The equal-width bin grid of the pipeline -/















/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/






open HumpFittedCurvature in
theorem solution(hg : ConcaveOn ℝ S g) (h1 : r₁ ∈ S) (h2 : r₂ ∈ S)
    (hr : r₁ < r₂) {y : ℝ} (hyS : y ∈ S) :
    (g y - chord g r₁ r₂ y) * ((y - r₁) * (y - r₂)) ≤ 0 := by
  rcases lt_trichotomy y r₁ with hlt | heq | hgt
  · have hres : g y - chord g r₁ r₂ y ≤ 0 := by
      linarith [le_chord_of_lt hg h2 hr hyS hlt]
    have hq : 0 ≤ (y - r₁) * (y - r₂) := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hres hq
  · subst heq
    simp
  · rcases le_or_gt y r₂ with hle | hgt2
    · have hres : 0 ≤ g y - chord g r₁ r₂ y := by
        linarith [chord_le_of_mem_Icc hg h1 h2 hr (mem_Icc.2 ⟨le_of_lt hgt, hle⟩)]
      have hq : (y - r₁) * (y - r₂) ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hres hq
    · have hres : g y - chord g r₁ r₂ y ≤ 0 := by
        linarith [le_chord_of_gt hg h1 hr hyS hgt2]
      have hq : 0 ≤ (y - r₁) * (y - r₂) := by nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg hres hq
