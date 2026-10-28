-- Prove2me | Theorems.Thm_ZetaReflection_EMOff_em_zeta_order_ext
-- name    : ZetaReflection.EMOff.em_zeta_order_ext
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:09:49.596518+00:00
-- url     : https://prove2.me/theorems/f572f3aa-40e4-4a50-8c5e-9bc39ae2c03b
-- title:
--   Extended general-order Euler–Maclaurin identity
-- statement:
--   Let $m,N\ge1$, and let $s\in\mathbb C$ satisfy $\operatorname{Re}s>1-m$ and
--   $s\ne1$. For the defined finite part $E_m$ and tail $T_m$,
--   $$\zeta(s)=E_m(s,N)+\frac{(-1)^{m-1}T_m(s,N)}{m!}.$$
--   This extends the higher-order identity to a wider half-plane.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCore.lean#L154-L206

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
import Theorems.Thm_ZetaReflection_EMHigh_em_zeta_order
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

theorem ZetaReflection.EMOff.em_zeta_order_ext (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 1 - (m : ℝ) < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = emFiniteM m s N + (-1) ^ (m - 1) * emTail s N m / (m ! : ℂ) := by sorry
