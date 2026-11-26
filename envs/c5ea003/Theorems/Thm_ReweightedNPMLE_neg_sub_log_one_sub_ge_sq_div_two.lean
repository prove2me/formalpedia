-- Prove2me | Theorems.Thm_ReweightedNPMLE_neg_sub_log_one_sub_ge_sq_div_two
-- name    : ReweightedNPMLE.neg_sub_log_one_sub_ge_sq_div_two
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:09.00382+00:00
-- url     : https://prove2.me/theorems/8554f5f0-1792-43c6-abdd-2875089f3b4c
-- title:
--   Quadratic lower bound for the lower Gamma rate function
-- statement:
--   For every real number $0\le t<1$, $$-t-\log(1-t)\ge t^2/2.$$ This is the lower-tail rate-function estimate used to control downward fluctuations of mean-one Gamma weights.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaBounds.lean#L48-L77

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Scalar inequalities for Gamma concentration

These are the two elementary logarithmic estimates used in Lemma 9.1 of the manuscript.
-/

open Set

theorem ReweightedNPMLE.neg_sub_log_one_sub_ge_sq_div_two {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    -t - Real.log (1 - t) ≥ t ^ 2 / 2 := by sorry
