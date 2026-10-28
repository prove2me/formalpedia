-- Prove2me | Theorems.Thm_ZetaReflection_emZetaClosed_eq_riemannZeta_of_one_lt
-- name    : ZetaReflection.emZetaClosed_eq_riemannZeta_of_one_lt
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:42.50091+00:00
-- url     : https://prove2.me/theorems/3e1ab621-1677-4222-a6c0-289f6fb74c66
-- title:
--   Closed Euler–Maclaurin expression equals zeta
-- statement:
--   For $s\in\mathbb C$ with $\operatorname{Re}s>1$, the defined closed
--   Euler–Maclaurin expression satisfies
--   $$\operatorname{emZetaClosed}(s)=\zeta(s).$$
--   This gives agreement with zeta in the half-plane of absolute convergence.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaComplex.lean#L433-L449

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Theorems.Thm_ZetaReflection_em_zeta_cpow
/-  EMZetaComplex.lean -- A2 Theorem 1, E-track: the COMPLEX Euler-Maclaurin representation of ζ
    and its K=1 analytic continuation into the critical strip.

    Builds on `EMZeta.lean` (real-s EM chain, Parts A-D', kernel-clean).  This file is the
    complex lift and the analytic continuation:

      E1.  `em_unit_step_cpow`   -- one-step EM over [m,m+1] for a ℂ-valued C¹ function.
           `em_cpow_partial`      -- finite-N EM for `f x = (x:ℂ)^(-s)`, s : ℂ, on [1,N].
      E2.  `em_zeta_cpow`         -- N→∞ complex representation, valid Re s > 1, tied to riemannZeta.
      E3.  `em_zeta_strip`        -- K=1 analytic continuation to 0 < Re s (s ≠ 1) with explicit
                                     remainder bound (THE PRIZE — covers the critical strip).
      E4.  `em_zeta_strip_enclosure` -- evaluator-facing finite-sum + explicit-tail enclosure shape.

    Only fully-proven, sorry-free lemmas live here.  General-K (K ≥ 2) stays in EMZetaWip.lean.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin + identity
    theorem), NOT a proof of RH.
-/




open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection

/-! ## E1a. One-step Euler-Maclaurin over a unit cell, ℂ-valued integrand.

    Direct lift of `em_unit_step`: the saw antiderivative `w x = x - m - 1/2` is real, cast to ℂ,
    and the IBP `intervalIntegral.integral_deriv_mul_eq_sub` runs in the `NormedRing ℂ`. -/



/-! ## E1b. Summed complex EM over an integer window, and the partial-ζ identity.

    Lift of `euler_maclaurin_one_window` to ℂ-valued `f`.  The telescoping and per-cell
    integrability arguments are identical to the real proof; the trapezoid bookkeeping is over ℂ. -/









/-! ## E2. The `N → ∞` complex representation for `Re s > 1`, tied to `riemannZeta`.

    Lift of `em_zeta_real` (Part D').  The three limits: partial sum → tsum (`summable_one_div_
    nat_cpow`), the two finite integrals → improper (`intervalIntegral_tendsto_integral_Ioi`),
    endpoint `N^{-s} → 0` (norm → 0).  Then `zeta_eq_tsum_one_div_nat_cpow` ties it to `ζ`. -/









/-! ## E3. K=1 analytic continuation into the critical strip (THE PRIZE).

    Define the EM closed form on `{Re s > 0}`:
        emZetaRemainder s := ∫_1^∞ (sawBernoulli 1 x)·(−s·x^{−s−1})   -- converges for Re s > 0
        emZetaClosed s     := 1/(s−1) + 1/2 + emZetaRemainder s
    For `Re s > 1`, `∫_1^∞ x^{−s} = 1/(s−1)` and `1^{−s} = 1`, so `emZetaClosed s = riemannZeta s`
    (from `em_zeta_cpow_riemannZeta`).  Both `riemannZeta` and `emZetaClosed` are analytic on
    `{Re s > 0} \ {1}`, agree on the open set `{Re s > 1}` (which has accumulation points in the
    larger strip), so by the identity theorem they agree on all of `{Re s > 0} \ {1}`.  That is
    `em_zeta_strip`, which covers the whole critical strip. -/

theorem ZetaReflection.emZetaClosed_eq_riemannZeta_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    emZetaClosed s = riemannZeta s := by sorry
