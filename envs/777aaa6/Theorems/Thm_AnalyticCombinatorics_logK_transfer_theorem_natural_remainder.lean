-- Prove2me | Theorems.Thm_AnalyticCombinatorics_logK_transfer_theorem_natural_remainder
-- name    : AnalyticCombinatorics.logK_transfer_theorem_natural_remainder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:43:02.563425+00:00
-- url     : https://prove2.me/theorems/cc4633b6-fac5-4d06-905c-df20f9ce2ca9
-- title:
--   Logarithmic-power transfer with its natural local remainder
-- statement:
--   Let $\alpha\in\mathbb R$ satisfy $\alpha>1$, let $C\in\mathbb C$ be nonzero, let $R>1$, $0<\varphi<\pi/2$, and fix a natural $k\ge1$. On $\Delta=\{z:|z|<R,\ \varphi<|\arg(z-1)|\}$ suppose $f$ is analytic on a neighborhood of every point and has the specified Taylor series $p$ at zero. If $|f(z)-C(1-z)^{-\alpha}(-\operatorname{Log}(1-z))^k|\,|1-z|^\alpha/(\log(1/|1-z|))^k\to0$ as $z\to1$ within $\Delta$, then, as natural $n\to\infty$,
--
--   $$p.\mathrm{coeff}(n)\sim \frac{C n^{\alpha-1}(\log n)^k}{\Gamma_{\mathbb R}(\alpha)}.$$
--
--   The real scale is embedded in $\mathbb C$. The model uses principal complex logarithms and powers; the remainder divisor and coefficient scale use the real logarithm.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogKTransferNatural.lean#L25. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogKFaithful
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# General logᵏ transfer — natural-remainder form

Capstone of the general logᵏ singularity hierarchy.  For `k ≥ 1`, the natural residual
`o(|1-z|^{-α}·log^k(1/|1-z|))`:

  f - C·(1-z)^{-α}·(-log(1-z))^k = o(|1-z|^{-α}·log^k(1/|1-z|))
    ⟹  [zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)^k.

Generalizes `logSq_transfer_theorem_natural_remainder` (k = 2) to arbitrary `k ≥ 1`,
built on LogKCoeff (coefficient identity), LogKFaithful (faithfulness), LogKAsymp
(asymptotic scale), and the logᵏ-weighted little-o circle transfer in LittleOTransfer.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics end AnalyticCombinatorics
open AnalyticCombinatorics

theorem AnalyticCombinatorics.logK_transfer_theorem_natural_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (k : ℕ) (hk : 1 ≤ k)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logKSingularityFun (α : ℂ) k z‖ * ‖(1 : ℂ) - z‖ ^ α
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) := by sorry
