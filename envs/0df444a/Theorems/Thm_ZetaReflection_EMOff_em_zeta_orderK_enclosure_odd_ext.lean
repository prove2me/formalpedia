-- Prove2me | Theorems.Thm_ZetaReflection_EMOff_em_zeta_orderK_enclosure_odd_ext
-- name    : ZetaReflection.EMOff.em_zeta_orderK_enclosure_odd_ext
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:13:23.052749+00:00
-- url     : https://prove2.me/theorems/68a91e79-ef45-4f03-94cd-6d14c01d22e7
-- title:
--   Extended odd-order Euler–Maclaurin enclosure
-- statement:
--   Let $K,N\ge1$ and $s\in\mathbb C$ satisfy $\sigma=\operatorname{Re}s>-2K$ and
--   $s\ne1$. With $E_K=\operatorname{emFinite}(K,s,N)$ and the defined rising
--   factorial $(s)_k$,
--   $$|\zeta(s)-E_K|\le
--   \frac{2(1+(\pi^2/6-1)/2^{2K-1})}{(2\pi)^{2K+1}}
--   \frac{|(s)_{2K+1}|N^{-(\sigma+2K)}}{\sigma+2K}.$$
--   This supplies the odd-order enclosure on both sides of the critical line.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCore.lean#L248-L284

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Theorems.Thm_ZetaReflection_EMHigh_abs_bernoulliFun_odd_le
import Theorems.Thm_ZetaReflection_EMHigh_emFinite_eq_emFiniteM
import Theorems.Thm_ZetaReflection_EMOff_em_zeta_order_ext
import Theorems.Thm_ZetaReflection_em_tail_integral_bound
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaOfflineCore.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 / K2): the general-order Euler-Maclaurin representation of ζ OFF the critical line.

    `EMZetaHigh.em_zeta_order` proves the order-`m` identity
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!
    on `Re s > 0` only (it is transported from the K = 1 continuation `em_zeta_strip`).  The tail
    integral converges on the larger half-plane `Re s > 1 - m`, so the identity extends there by the
    identity theorem.  This file proves that extension and the resulting remainder bounds for
    every real part `σ > 1 - 2K` (even saw) and `σ > -2K` (odd saw):

      O1.  `emTail_eq_mellin`        -- the tail is `emC s m · mellin (sawCut m N) (1 - s - m)`;
      O2.  `emTail_differentiableAt` -- hence complex-differentiable on `Re s > 1 - m`
                                        (`mellin_differentiableAt_of_isBigO_rpow`);
      O3.  `emFiniteM_differentiableAt` -- the finite part is differentiable off `s = 1`;
      O4.  `em_zeta_order_ext`       -- THE CONTINUATION: the order-`m` identity on `Re s > 1 - m`,
                                        `s ≠ 1` (identity theorem on the convex strip
                                        `1 - m < Re s < 1`, anchored at `s = 1/2`);
      O5.  `em_zeta_orderK_enclosure_ext`, `em_zeta_orderK_enclosure_odd_ext` -- the general-K
                                        remainder bounds of `EMZetaHigh` for `σ > 1 - 2K`,
                                        resp. `σ > -2K` (so `σ = -1` is covered from `K = 1` on).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin + analytic
    continuation); it says nothing about the Riemann Hypothesis.
-/


open MeasureTheory Set Filter Topology Complex
open scoped Real Nat

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

section
namespace ZetaReflection.EMOff
end ZetaReflection.EMOff
open ZetaReflection.EMOff

open EMHigh

/-! ## O1. The tail as a Mellin transform. -/





/-! ## O2. Differentiability of the tail on `Re s > 1 - m`. -/













/-! ## O3. Differentiability of the finite part off `s = 1`. -/



/-! ## O4. THE CONTINUATION of the order-`m` identity to `Re s > 1 - m`. -/



/-! ## O5. The general-K remainder bounds off the critical line. -/

theorem ZetaReflection.EMOff.em_zeta_orderK_enclosure_odd_ext (K : ℕ) (hK : 1 ≤ K) {s : ℂ}
    (hs : -((2 * K : ℕ) : ℝ) < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) := by sorry
