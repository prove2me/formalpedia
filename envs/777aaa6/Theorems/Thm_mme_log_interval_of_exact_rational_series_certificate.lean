-- Prove2me | Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
-- name    : mme_log_interval_of_exact_rational_series_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:11:57.57778+00:00
-- url     : https://prove2.me/theorems/f79fd5f9-9d45-427a-a128-f81b83b98053
-- title:
--   Exact rational series certificates imply rigorous natural-logarithm intervals
-- statement:
--   Let $q,t,L,U$ be rational numbers and $k,n$ natural numbers. Assume $q>0$, $0\le t<1$, and $q2^k=(1+t)/(1-t)$. Define the finite rational sum $S_n(t)=\sum_{i=0}^{n-1}t^{2i+1}/(2i+1)$, and let $a=69314718055/10^{11}$ and $b=69314718057/10^{11}$. If the exact rational inequalities
--
--   $$L+kb\le2S_n(t),\qquad 2\left(S_n(t)+\frac{t^{2n+1}}{1-t^2}\right)-ka\le U$$
--
--   hold, then
--
--   $$L\le\log q\le U.$$
--
--   Every certificate hypothesis is a rational equality or inequality, with no assumed logarithm bound. This provides a kernel-checkable interface for individual logarithms in a rational numerical witness. It does not assert that the complete matrix-multiplication witness has already passed those checks.
-- source:
--   Finite atanh-series logarithm bounds Real.sum_range_le_log_div and Real.log_div_le_sum_range_add from pinned Mathlib Analysis.SpecialFunctions.Log.Deriv, combined with dyadic scaling. Reuses the same 12-term log(2) certificate and range-reduction method used in the prior Stothers/DWZ numerical proofs; implemented directly from Mathlib without importing research-alias proof modules. Intended for exact entropy/logarithm certification of the released More Asymmetry fourth-power witness, https://arxiv.org/abs/2404.16349v2, Section 7. This is a numerical-certificate soundness lemma, not a separate source-paper exponent result.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open BigOperators Finset

set_option autoImplicit false

theorem mme_log_interval_of_exact_rational_series_certificate
    (q t lo hi : ℚ) (k n : ℕ)
    (hq : 0 < q) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hscale : q * 2 ^ k = (1 + t) / (1 - t))
    (hlo : lo + k * (69314718057 / 100000000000 : ℚ) ≤
      2 * ∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1))
    (hhi : 2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
      t ^ (2 * n + 1) / (1 - t ^ 2)) -
      k * (69314718055 / 100000000000 : ℚ) ≤ hi) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  sorry
