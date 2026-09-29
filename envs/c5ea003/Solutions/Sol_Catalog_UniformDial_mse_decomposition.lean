-- Prove2me | solution 1 for Catalog.UniformDial.mse_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:24.978704+00:00
-- url     : https://prove2.me/submissions/db330949-2574-40f7-aec5-3c8c8d2dacf2

-- Sol generated from Combinatorics/UniformDialYieldRegression.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Definitions.Def_Combinatorics_UniformDialYieldRegression
/-
# The yield dial as a regressor: explained variance, augmentation, and regime invariance

Companion to `Combinatorics.UniformDialDrawInvariance`.  There the *sign* of the dial was
shown to be draw-regime invariant; here we analyse the *variance-share* (R²) statistic
that the experiment reports, in the same finite-population / arbitrary-draw-regime setting.

Main results.

* `mse_decomposition` — the exact bias/variance decomposition of the weighted mean squared
  error of an affine predictor `a + b·x` of the rate `y`.
* `mse_optimal`, `mse_ge_optimal` — the ordinary-least-squares optimum and its value
  `Var y − Cov² / Var x`, valid in every draw regime.
* `wcov_sq_le` — weighted Cauchy–Schwarz, obtained as a *corollary* of the optimality
  statement; hence `R2_nonneg`, `R2_le_one`: the variance share is a genuine share.
* `mse_optimal_eq_R2` — `min MSE = Var y · (1 − R²)`, the identity that makes R² the
  "yield dial" reading.
* `augment_strict_gain` — adding a second regressor `z` to the fit strictly lowers the
  residual error, by exactly `⟨r,z⟩²/‖z‖²`, whenever the residual is not orthogonal to `z`.
  This is the *augmented* R² of the experiment, and the gain formula is regime-explicit.
* `footprint_beats_count_uniform`, `footprint_beats_count_unbalanced` — a concrete
  four-key population on which footprint weighting beats plain count by more than `0.2`
  under a uniform regime and by more than `0.13` under a `(0.7, 0.1, 0.1, 0.1)` regime:
  the ordering of the two dials survives a genuinely unbalanced draw, while the numerical
  gap does move.  `footprint_count_regimes_far` records that the two regimes are far
  apart in ℓ¹, so this is not a perturbative statement.
-/

open Finset

open Catalog.UniformDial

variable {ι : Type*} [Fintype ι]


lemma centered_sum_eq_zero {p x : ι → ℝ} (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - wmean p x) = 0 := by
  have : ∀ i, p i * (x i - wmean p x) = p i * x i - wmean p x * p i :=
    fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, ← Finset.mul_sum, hp,
    mul_one]
  simp [wmean]













/-! ### Exact drivers: when the footprint *is* the mechanism -/






/-! ### A concrete four-key population, measured in two very different draw regimes -/




















open Catalog.UniformDial in
theorem solution{p x y : ι → ℝ} (hp : ∑ i, p i = 1) (a b : ℝ) :
    mse p x y a b = wvar p y - 2 * b * wcov p x y + b ^ 2 * wvar p x
      + (wmean p y - a - b * wmean p x) ^ 2 := by
  set mx := wmean p x with hmx
  set my := wmean p y with hmy
  set c := my - a - b * mx with hc
  have hx0 : ∑ i, p i * (x i - mx) = 0 := centered_sum_eq_zero hp
  have hy0 : ∑ i, p i * (y i - my) = 0 := centered_sum_eq_zero hp
  have expand : ∀ i, p i * (y i - (a + b * x i)) ^ 2
      = p i * (y i - my) * (y i - my) + b ^ 2 * (p i * (x i - mx) * (x i - mx))
        - 2 * b * (p i * (x i - mx) * (y i - my)) + 2 * c * (p i * (y i - my))
        - 2 * b * c * (p i * (x i - mx)) + c ^ 2 * p i := by
    intro i
    have : y i - (a + b * x i) = (y i - my) - b * (x i - mx) + c := by rw [hc]; ring
    rw [this]; ring
  rw [mse, Finset.sum_congr rfl fun i _ => expand i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hx0, hy0, hp,
    mul_zero, mul_one, add_zero, sub_zero]
  simp only [wvar, wcov, ← hmx, ← hmy]
  ring
