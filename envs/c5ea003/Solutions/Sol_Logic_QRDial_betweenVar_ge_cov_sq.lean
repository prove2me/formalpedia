-- Prove2me | solution 1 for Logic.QRDial.betweenVar_ge_cov_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:59:09.359912+00:00
-- url     : https://prove2.me/submissions/17297d06-05c7-4c9f-9f99-4506b72daf93

-- Sol generated from Logic/QRDialDispersionLaws.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Theorems.Thm_Logic_QRDial_avg_add
import Theorems.Thm_Logic_QRDial_avg_const
import Theorems.Thm_Logic_QRDial_avg_mul_left
import Theorems.Thm_Logic_QRDial_cov_eq
import Theorems.Thm_Logic_QRDial_sum_sq_dev_cell
import Theorems.Thm_Logic_QRDial_var_decomposition
import Theorems.Thm_Logic_QRDial_var_eq
/-
# Dispersion accounting for a covariate dial: how much overdispersion can a dial explain?

This file supplies the exact finite-sample laws behind the FACT round-78 experiment
(exp 576, paper 226) in which a per-`N` hit count over 128 balanced bitlen-96 semiprimes
shows a variance-to-mean ratio `D_raw = 7.27` (Poisson would give `1`), and three
small-prime quadratic-residue "dials" are regressed against the per-`N` log rates.

The experiment reports two numbers per dial: a regression `R²` and a *dispersion
reduction* `D-red`.  The pre-registered H1 bar was `R² ≥ 0.25` **and** `D-red ≥ 30%`.
Measured: `R² = 0.0127 / 0.0781 / 0.0565` and `D-red = 0.88% / 14.22% / 9.07%`.

What is proved here is the mathematics that makes those two numbers comparable and that
turns "the dial misses the bar" into a *theorem* about every dial-based recalibration,
not merely about the particular fit that was run:

* `Logic.QRDial.mse_lower_bound` / `Logic.QRDial.mse_ols_eq` — the least-squares residual
  of *any* affine recalibration `y ↦ a + b·s` of a dial `s` is at least
  `var y − cov(y,s)² / var s`, with equality at the OLS coefficients.  So the linear
  explained fraction is exactly the squared correlation `r²`; no re-tuning of the dial's
  slope can do better (`Logic.QRDial.linear_capture_bound`).

* `Logic.QRDial.var_decomposition` — the exact ANOVA identity
  `var = withinVar + betweenVar` for the partition of the sample into the level sets of
  the dial, together with `Logic.QRDial.conditional_mean_optimal`: conditioning on the
  dial's level sets is the *best possible* use of the dial, linear or not.  Hence
  `Logic.QRDial.corr_sq_le_eta_sq`: `r² ≤ η²`, which is why the measured `D-red` (14.22%)
  can and does exceed the linear `R²` (7.81%).

* `Logic.QRDial.disp_reduction_eq_eta_sq` — the dispersion reduction achievable by a dial
  is *exactly* its explained-variance fraction `η²`.  This is the identification that lets
  the two H1 legs be compared at all.

* `Logic.QRDial.poisson_mixture_disp` — under Poisson calibration inside each dial cell,
  `D = 1 + betweenVar / mean`: all overdispersion is between-cell heterogeneity.

* `Logic.QRDial.exp576_residual_dispersion` and
  `Logic.QRDial.exp576_unexplained_excess_fraction` — the certified numeric readings of
  exp 576: from `D_raw = 7.27` and `η² ≤ 0.1422`, the residual dispersion is `≥ 6.23` and
  at least `83%` of the Poisson excess `D − 1` survives the dial, so the H1 bar of `30%`
  is missed by every dial-based recalibration, not just by the fitted one.

Everything is finite-sample and exact; no asymptotics and no distributional assumption
beyond the explicitly stated Poisson-calibration hypothesis.
-/

open Finset

open Logic.QRDial

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Sample averages, variances, covariances -/















/-! ## Affine recalibration of a dial: the linear capture bound -/


/-- Exact expansion of the recalibration error. -/
lemma mse_expand (y s : ι → ℝ) (a b : ℝ) :
    mse y s a b = var y - 2 * b * cov y s + b ^ 2 * var s
      + (avg y - a - b * avg s) ^ 2 := by
  have h : (fun i => (y i - (a + b * s i)) ^ 2)
      = fun i => (y i * y i) + ((-2 * b) * (y i * s i)
        + ((b * b) * (s i * s i) + ((-2 * a) * y i + ((2 * a * b) * s i + a ^ 2)))) := by
    funext i; ring
  rw [mse, h]
  simp only [avg_add, avg_mul_left, avg_const]
  rw [var_eq, var_eq, cov_eq]
  ring


/-- The bound of `mse_lower_bound` is attained at the ordinary least squares coefficients. -/
theorem mse_ols_eq (y s : ι → ℝ) (hs : 0 < var s) :
    mse y s (avg y - (cov y s / var s) * avg s) (cov y s / var s)
      = var y - (cov y s) ^ 2 / var s := by
  rw [mse_expand]
  field_simp
  ring





/-! ## Conditioning on the dial's level sets: the ANOVA decomposition -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]




omit [Nonempty ι] in
/-- Summing over cells and then within cells is summing pointwise. -/
lemma sum_cellwise (g : ι → κ) (f : ι → ℝ) : ∑ k, ∑ i ∈ cell g k, f i = ∑ i, f i := by
  simpa [cell] using Finset.sum_fiberwise (Finset.univ : Finset ι) g f

omit [Nonempty ι] in
/-- The cell-dependent version: inside the cell labelled `k` the label may be read off
from the index. -/
lemma sum_cellwise_dep (g : ι → κ) (f : ι → κ → ℝ) :
    ∑ k, ∑ i ∈ cell g k, f i k = ∑ i, f i (g i) := by
  rw [← sum_cellwise g (fun i => f i (g i))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
  have hk : g i = k := by simpa [cell] using hi
  rw [hk]


omit [Nonempty ι] in
/-- **Conditional means are optimal.**  Replacing each observation by the mean of its dial
cell beats every other cell-measurable predictor `h`. -/
theorem conditional_mean_optimal (x : ι → ℝ) (g : ι → κ) (h : κ → ℝ) :
    ∑ i, (x i - cellMean x g (g i)) ^ 2 ≤ ∑ i, (x i - h (g i)) ^ 2 := by
  rw [← sum_cellwise_dep g (fun i k => (x i - cellMean x g k) ^ 2),
    ← sum_cellwise_dep g (fun i k => (x i - h k) ^ 2)]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [sum_sq_dev_cell (cell g k) x (h k)]
  have hnn : (0:ℝ) ≤ (cell g k).card * ((∑ j ∈ cell g k, x j) / (cell g k).card - h k) ^ 2 := by
    positivity
  have hcm : cellMean x g k = (∑ j ∈ cell g k, x j) / (cell g k).card := rfl
  rw [hcm]
  linarith









/-! ## Dispersion: what a dial can and cannot remove -/





/-! ## Certified numeric readings of exp 576 -/





open Logic.QRDial in
theorem solution(y s : ι → ℝ) (g : ι → κ) (phi : κ → ℝ)
    (hs : ∀ i, s i = phi (g i)) (hsv : 0 < var s) :
    (cov y s) ^ 2 / var s ≤ betweenVar y g := by
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) := by
    have := Fintype.card_pos (α := ι); positivity
  set b : ℝ := cov y s / var s with hbdef
  set a : ℝ := avg y - b * avg s with hadef
  have hopt := conditional_mean_optimal y g (fun k => b * phi k + a)
  have hmse : mse y s a b
      = (∑ i, (y i - (b * phi (g i) + a)) ^ 2) / (Fintype.card ι : ℝ) := by
    rw [mse, avg]
    refine congrArg (fun t => t / (Fintype.card ι : ℝ)) (Finset.sum_congr rfl fun i _ => ?_)
    rw [hs i]; ring_nf
  have hwithin : withinVar y g
      = (∑ i, (y i - cellMean y g (g i)) ^ 2) / (Fintype.card ι : ℝ) := rfl
  have hle : withinVar y g ≤ mse y s a b := by
    rw [hwithin, hmse]
    gcongr
  rw [hadef, hbdef, mse_ols_eq y s hsv] at hle
  have hdec := var_decomposition y g
  linarith
