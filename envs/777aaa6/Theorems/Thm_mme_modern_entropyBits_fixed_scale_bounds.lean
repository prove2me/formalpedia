-- Prove2me | Theorems.Thm_mme_modern_entropyBits_fixed_scale_bounds
-- name    : mme_modern_entropyBits_fixed_scale_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T08:24:02.919407+00:00
-- url     : https://prove2.me/theorems/f17db260-b5ab-45b9-bcd7-32b0c5d4acbd
-- title:
--   Certified base-two entropy bounds from fixed-scale integer checks
-- statement:
--   Let $S,d$ be positive integers, and let $p_i,k_i$ be natural numbers indexed by a finite set of size $m$. For every nonzero count assume $d\le p_i2^{k_i}\le2d$. Write
--
--   $$H_2=\frac{\sum_i -(p_i/d)\log(p_i/d)}{\log2},$$
--
--   with the zero-term convention. Let $(E_L,E_U)$ be the computed integer entropy endpoints at scale $Sd$, and let $(B_L,B_U)$ be the computed endpoints for $\log2$ at scale $S$.
--
--   Choose nonnegative integers $q_L,q_U$ and positive integers $r_L,r_U$. If the two exact integer checks hold,
--
--   $$q_LdB_U<r_LE_L,\qquad r_UE_U<q_UdB_L,$$
--
--   then
--
--   $$\frac{q_L}{r_L}<H_2<\frac{q_U}{r_U}.$$
--
--   This provides strict bounds on the existing base-two entropy expression from finite integer checks. If $\sum_i p_i=d$, it is the Shannon entropy of a rational probability distribution; normalization is not needed for the displayed entropy-sum inequality itself. No matrix-multiplication witness or exponent bound is asserted.
-- source:
--   Supporting numerical-verification construction for Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884v1, Section 4, https://arxiv.org/html/2608.16884v1#S4. The fixed-scale evaluator is an auxiliary construction, not a claim stated in that paper. Its analytic foundation is Mathlib 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e, Analysis/SpecialFunctions/Log/Deriv.lean, Real.sum_range_le_log_div and Real.log_div_le_sum_range_add.

import Definitions.Def_mme_dyadic_log_interval
import Definitions.Def_mme_modern_entropy_data
open MME.DyadicLog
set_option autoImplicit false

theorem mme_modern_entropyBits_fixed_scale_bounds {m S d n qL rL qU rU : ℕ}
    (hS : 0 < S) (hd : 0 < d) (hrL : 0 < rL) (hrU : 0 < rU)
    (counts shifts : Fin m → ℕ)
    (hcheck : rangeReductionCheck d (List.ofFn (fun i ↦ (counts i, shifts i))) = true)
    (hlower : (qL : ℤ) * d * (unitLog S 2 1 n).hi <
      (rL : ℤ) * (entropyInterval S d n
        (List.ofFn (fun i ↦ (counts i, shifts i)))).lo)
    (hupper : (rU : ℤ) * (entropyInterval S d n
        (List.ofFn (fun i ↦ (counts i, shifts i)))).hi <
      (qU : ℤ) * d * (unitLog S 2 1 n).lo) :
    (qL : ℝ) / (rL : ℝ) < mme_modern_entropyBits (fun i ↦ (counts i : ℝ) / d) ∧
      mme_modern_entropyBits (fun i ↦ (counts i : ℝ) / d) < (qU : ℝ) / (rU : ℝ) := by sorry
