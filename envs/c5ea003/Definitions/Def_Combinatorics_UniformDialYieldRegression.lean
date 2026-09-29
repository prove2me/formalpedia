-- Prove2me | Definitions.Def_Combinatorics_UniformDialYieldRegression
-- name    : Combinatorics_UniformDialYieldRegression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:57:02.711322+00:00
-- url     : https://prove2.me/theorems/71014ece-7649-48cb-8c56-73098e342d8e
-- title:
--   Aether Catalog definitions — Combinatorics_UniformDialYieldRegression
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.UniformDialYieldRegression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/UniformDialYieldRegression.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
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

namespace Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

/-- Weighted mean squared error of the affine predictor `a + b * x` for the rate `y`. -/
noncomputable def mse (p x y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, p i * (y i - (a + b * x i)) ^ 2








/-- The variance share (R²) of the dial `x` for the rate `y` in draw regime `p`. -/
noncomputable def R2 (p x y : ι → ℝ) : ℝ := (wcov p x y) ^ 2 / (wvar p x * wvar p y)






/-! ### Exact drivers: when the footprint *is* the mechanism -/






/-! ### A concrete four-key population, measured in two very different draw regimes -/

section Example

/-- Footprint weights of four keys. -/
def fw : Fin 4 → ℝ := ![1, 2, 4, 8]

/-- Plain counts of the same four keys. -/
def fc : Fin 4 → ℝ := ![1, 1, 2, 2]

/-- Observed yield rates. -/
def fy : Fin 4 → ℝ := ![1, 2, 5, 9]

/-- The uniform (balanced) draw regime. -/
noncomputable def pU : Fin 4 → ℝ := ![1/4, 1/4, 1/4, 1/4]

/-- A genuinely unbalanced draw regime. -/
noncomputable def pQ : Fin 4 → ℝ := ![7/10, 1/10, 1/10, 1/10]

lemma pU_nonneg (i : Fin 4) : 0 ≤ pU i := by
  fin_cases i <;> norm_num [pU]

lemma pQ_nonneg (i : Fin 4) : 0 ≤ pQ i := by
  fin_cases i <;> norm_num [pQ]

lemma pU_total : ∑ i, pU i = 1 := by
  norm_num [pU, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

lemma pQ_total : ∑ i, pQ i = 1 := by
  norm_num [pQ, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]





/-- The uniform regime as a `DrawRegime`. -/
noncomputable def regU : DrawRegime (Fin 4) := ⟨pU, pU_nonneg, pU_total⟩

/-- The unbalanced regime as a `DrawRegime`. -/
noncomputable def regQ : DrawRegime (Fin 4) := ⟨pQ, pQ_nonneg, pQ_total⟩


end Example

end Catalog.UniformDial


