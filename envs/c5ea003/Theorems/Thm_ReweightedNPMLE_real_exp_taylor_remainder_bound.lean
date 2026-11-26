-- Prove2me | Theorems.Thm_ReweightedNPMLE_real_exp_taylor_remainder_bound
-- name    : ReweightedNPMLE.real_exp_taylor_remainder_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:35:55.909468+00:00
-- url     : https://prove2.me/theorems/fb9b5c4b-0ff9-44ba-a43a-4cc61165b30e
-- title:
--   Uniform exponential Taylor remainder on a symmetric interval
-- statement:
--   For an integer $m\ge0$, $T\ge0$, and $|t|\le T$, $$\left|e^t-\sum_{\ell=0}^m\frac{t^\ell}{\ell!}\right|\le e^T\frac{T^{m+1}}{(m+1)!}.$$ This is the scalar approximation estimate used to construct the Gaussian effective-dimensional subspace.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Taylor.lean#L31-L52

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

/-!
# Quantitative exponential approximation

Exact Taylor and factorial bounds used in Proposition 4.1 and Lemma 8.1 of the manuscript.
-/



open Finset Set

theorem ReweightedNPMLE.real_exp_taylor_remainder_bound (m : ℕ) {t T : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) :
    |Real.exp t - ∑ ell ∈ range (m + 1), t ^ ell / ell.factorial| ≤
      Real.exp T * T ^ (m + 1) / (m + 1).factorial := by sorry
