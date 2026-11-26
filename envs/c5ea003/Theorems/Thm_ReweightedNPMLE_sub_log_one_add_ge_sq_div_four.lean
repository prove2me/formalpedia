-- Prove2me | Theorems.Thm_ReweightedNPMLE_sub_log_one_add_ge_sq_div_four
-- name    : ReweightedNPMLE.sub_log_one_add_ge_sq_div_four
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:24.066425+00:00
-- url     : https://prove2.me/theorems/8c087eca-98de-4d05-92a2-31ecbac00b50
-- title:
--   Quadratic lower bound for the upper Gamma rate function
-- statement:
--   For every real number $t\in[0,1]$, $$t-\log(1+t)\ge t^2/4.$$ This elementary estimate converts the exact upper Gamma Chernoff exponent into a quadratic concentration bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaBounds.lean#L15-L46

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Scalar inequalities for Gamma concentration

These are the two elementary logarithmic estimates used in Lemma 9.1 of the manuscript.
-/

open Set

theorem ReweightedNPMLE.sub_log_one_add_ge_sq_div_four {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t - Real.log (1 + t) ≥ t ^ 2 / 4 := by sorry
