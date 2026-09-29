-- Prove2me | Theorems.Thm_Logic_QRDial_sum_sq_dev_cell
-- name    : Logic.QRDial.sum_sq_dev_cell
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:32:54.941402+00:00
-- url     : https://prove2.me/theorems/d18f5ce6-818b-40fb-9876-a7cd44de6bb7
-- title:
--   Within a fixed finite set, squared deviations around an arbitrary centre split into
-- statement:
--   Within a fixed finite set, squared deviations around an arbitrary centre split into
--   squared deviations around the set's own mean plus a centre-offset term.
--
--   ```lean
--   theorem Logic.QRDial.sum_sq_dev_cell(F : Finset ι) (x : ι → ℝ) (m : ℝ) :
--       ∑ i ∈ F, (x i - m) ^ 2
--         = (∑ i ∈ F, (x i - (∑ j ∈ F, x j) / F.card) ^ 2)
--           + F.card * ((∑ j ∈ F, x j) / F.card - m) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QRDialDispersionLaws.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QRDialDispersionLaws.lean#L197

-- Thm stub generated from Logic/QRDialDispersionLaws.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
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









/-! ## Conditioning on the dial's level sets: the ANOVA decomposition -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]



omit [Fintype ι] [Nonempty ι] in

theorem Logic.QRDial.sum_sq_dev_cell(F : Finset ι) (x : ι → ℝ) (m : ℝ) :
    ∑ i ∈ F, (x i - m) ^ 2
      = (∑ i ∈ F, (x i - (∑ j ∈ F, x j) / F.card) ^ 2)
        + F.card * ((∑ j ∈ F, x j) / F.card - m) ^ 2 := by sorry
