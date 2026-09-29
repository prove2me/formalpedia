-- Prove2me | solution 1 for Logic.PhaseRoute.avg_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:25:15.094787+00:00
-- url     : https://prove2.me/submissions/b8dddde5-81e4-4615-9d86-0b2a61460ca3

-- Sol generated from Logic/PhaseRouteLeastSquares.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteLeastSquares
/-
# Finite-sample least squares: the exact incremental-`R²` calculus

This file builds, from scratch, the algebraic core needed to state and prove
*negative* results about feature encodings in a finite-sample linear model:

* `Logic.PhaseRoute.avg`, `cov`, `varr`   — empirical mean / covariance / variance,
* `Logic.PhaseRoute.msse`                — mean squared error of a predictor,
* `Logic.PhaseRoute.Rsq`                 — coefficient of determination against the
  constant (intercept-only) baseline.

The main results are exact identities, not inequalities-with-slack:

* `msse_decomp` : `msse y h = varr y - 2*cov y h + varr h + (avg y - avg h)^2`,
  the complete bias/variance/alignment split of the error of *any* predictor;
* `msse_ge_varr_of_cov_eq_zero` and its strict form `msse_gt_varr_of_cov_eq_zero`
  : a predictor uncorrelated with the target is *never* useful and is strictly
  harmful unless it is constant;
* `msse_affine_lower_bound` / `msse_affine_opt` : the optimal single-feature
  affine fit and its exact error, hence
* `Rsq_affine_le_corr_sq` / `Rsq_affine_opt_eq_corr_sq` : the best attainable
  `R²` of a one-feature model is *exactly* the squared empirical correlation.

As a by-product we derive Cauchy–Schwarz for the empirical covariance
(`cov_sq_le`) from the regression identity rather than the other way round.

This is the "dial" calculus used in `Logic.PhaseRouteAlignment` to prove that a
whole family of encodings is provably worthless while a degree-`2` interaction
encoding is provably perfect.
-/

open Logic.PhaseRoute

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]






lemma card_ne_zero : ((Fintype.card ι : ℝ)) ≠ 0 := by
  have : 0 < Fintype.card ι := Fintype.card_pos
  positivity

/-! ### Linearity of the empirical mean -/







/-! ### Variance -/





/-! ### The exact error decomposition -/








/-! ### Uncorrelated predictors are useless, and strictly harmful unless constant -/





/-! ### The optimal single-feature affine model -/











open Logic.PhaseRoute in
theorem solution{f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : avg f = 0 ↔ ∀ i, f i = 0 := by
  have h2 : ((Fintype.card ι : ℝ)) ≠ 0 := card_ne_zero
  constructor
  · intro h i
    have hs : (∑ i, f i) = 0 := by
      rw [avg, div_eq_zero_iff] at h
      rcases h with h | h
      · exact h
      · exact absurd h h2
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf j)).1 hs i (Finset.mem_univ i)
  · intro h
    simp [avg, h]
