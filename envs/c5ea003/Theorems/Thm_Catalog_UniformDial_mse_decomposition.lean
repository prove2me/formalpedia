-- Prove2me | Theorems.Thm_Catalog_UniformDial_mse_decomposition
-- name    : Catalog.UniformDial.mse_decomposition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:34.177584+00:00
-- url     : https://prove2.me/theorems/af2a9849-51dc-4f26-8c6f-e7f4f4134766
-- title:
--   Exact decomposition of the weighted MSE into rate variance, dial covariance,
-- statement:
--   **Exact decomposition of the weighted MSE** into rate variance, dial covariance,
--   dial variance and a squared calibration bias.
--
--   ```lean
--   theorem Catalog.UniformDial.mse_decomposition{p x y : ι → ℝ} (hp : ∑ i, p i = 1) (a b : ℝ) :
--       mse p x y a b = wvar p y - 2 * b * wcov p x y + b ^ 2 * wvar p x
--         + (wmean p y - a - b * wmean p x) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UniformDialYieldRegression.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UniformDialYieldRegression.lean#L57

-- Thm stub generated from Combinatorics/UniformDialYieldRegression.lean
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

theorem Catalog.UniformDial.mse_decomposition{p x y : ι → ℝ} (hp : ∑ i, p i = 1) (a b : ℝ) :
    mse p x y a b = wvar p y - 2 * b * wcov p x y + b ^ 2 * wvar p x
      + (wmean p y - a - b * wmean p x) ^ 2 := by sorry
