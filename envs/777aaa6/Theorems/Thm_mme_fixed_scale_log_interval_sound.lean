-- Prove2me | Theorems.Thm_mme_fixed_scale_log_interval_sound
-- name    : mme_fixed_scale_log_interval_sound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T08:24:03.21745+00:00
-- url     : https://prove2.me/theorems/f4ab7992-14de-4bdc-9cd0-9a27a526458f
-- title:
--   Soundness of the fixed-scale integer logarithm evaluator
-- statement:
--   Let $S,p,d$ be positive integers and $k,n$ natural numbers. Assume
--
--   $$d\le p2^k\le2d.$$
--
--   Let $(L,U)$ be the integer endpoints returned by the fixed-scale logarithm evaluator with scale $S$ and $n$ series terms, including all directed-rounding and remainder allowances. Then
--
--   $$L\le S\log(p/d)\le U.$$
--
--   The endpoints are computed using integer arithmetic. The theorem therefore turns an executable finite calculation into certified logarithm bounds, with precision chosen by the caller. It is an auxiliary checker soundness result; it does not assert that an AlphaEvolve witness exists or passes verification.
-- source:
--   Supporting numerical-verification construction for Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884v1, Section 4, https://arxiv.org/html/2608.16884v1#S4. The fixed-scale evaluator is an auxiliary construction, not a claim stated in that paper. Its analytic foundation is Mathlib 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e, Analysis/SpecialFunctions/Log/Deriv.lean, Real.sum_range_le_log_div and Real.log_div_le_sum_range_add.

import Definitions.Def_mme_dyadic_log_interval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MME.DyadicLog
set_option autoImplicit false

theorem mme_fixed_scale_log_interval_sound {S p d k n : ℕ} (hS : 0 < S) (hp : 0 < p) (hd : 0 < d)
    (hlo : d ≤ p * 2 ^ k) (hhi : p * 2 ^ k ≤ 2 * d) :
    (scaledLog S p d k n).Valid S (Real.log ((p : ℝ) / (d : ℝ))) := by sorry
