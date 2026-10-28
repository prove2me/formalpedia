-- Prove2me | Theorems.Thm_ZetaReflection_euler_maclaurin_one_window_cpow
-- name    : ZetaReflection.euler_maclaurin_one_window_cpow
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:45.261251+00:00
-- url     : https://prove2.me/theorems/aeee377d-2a00-4f7c-a086-f8d4e1283ba9
-- title:
--   First-order Euler–Maclaurin over an integer window
-- statement:
--   Let natural numbers $M\le N$ and functions $f,f_1:\mathbb R\to\mathbb C$
--   satisfy $f'=f_1$ on $[M,N]$, with $f_1$ interval-integrable on each unit
--   interval in the window. For the first periodic Bernoulli sawtooth $b_1$,
--   $$\sum_{n=M}^{N-1}f(n)=\int_M^N f(x)\,dx-\frac{f(N)-f(M)}2
--   +\int_M^N b_1(x)f_1(x)\,dx.$$
--   This is the finite-window formula used for the zeta series.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaComplex.lean#L106-L179

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
import Theorems.Thm_ZetaReflection_em_unit_step_cpow
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

theorem ZetaReflection.euler_maclaurin_one_window_cpow {f f' : ℝ → ℂ} (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt f (f' x) x)
    (hf' : ∀ k ∈ Finset.Ico M N, IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    (∑ n ∈ Finset.Ico M N, f (n : ℝ))
      = (∫ x in (M : ℝ)..N, f x) - (f N - f M) / 2
        + ∫ x in (M : ℝ)..N, (sawBernoulli 1 x : ℂ) * f' x := by sorry
