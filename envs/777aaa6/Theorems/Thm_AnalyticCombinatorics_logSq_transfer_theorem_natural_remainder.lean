-- Prove2me | Theorems.Thm_AnalyticCombinatorics_logSq_transfer_theorem_natural_remainder
-- name    : AnalyticCombinatorics.logSq_transfer_theorem_natural_remainder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:46:17.175834+00:00
-- url     : https://prove2.me/theorems/0990d0f4-3f50-4f57-aca7-a03fa5a00702
-- title:
--   Squared logarithmic transfer with the natural remainder
-- statement:
--   Let $C\in\mathbb C\setminus\{0\}$, $R>1$, $0<\phi<\pi/2$. Let $f$ have the specified formal multilinear power series $p$ at $0$, and be analytic on a neighbourhood of every point of the source dented domain $\Delta(R,\phi)$ (`DeltaDomainArg`). All limits at $1$ below are taken within that domain. Write $L_\alpha(z)=(1-z)^{-\alpha}[-\log(1-z)]$, with the source complex powers and logarithm. Fix a real $\alpha>1$. Replace $L_\alpha$ by $L^{(2)}_\alpha(z)=(1-z)^{-\alpha}[-\log(1-z)]^2$. Assume $$\frac{\lVert f(z)-CL^{(2)}_\alpha(z)\rVert\,|1-z|^\alpha}{[\log(1/|1-z|)]^{2}}\longrightarrow0.$$ Then $$p_n\sim C\,\frac{n^{\alpha-1}}{\Gamma(\alpha)}(\log n)^{2}.$$ The power-series, domain, nonzero-leading-coefficient and full weighted remainder assumptions are all retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogSqTransferNatural.lean#L23. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSqTransfer
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
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

namespace AnalyticCombinatorics end AnalyticCombinatorics

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Squared-logarithm transfer — natural-remainder form

Upgrades `logSq_transfer_theorem_strong_remainder` to the natural residual
`o(|1-z|^{-α}·log²(1/|1-z|))`:

  f - C·(1-z)^{-α}·(-log(1-z))² = o(|1-z|^{-α}·log²(1/|1-z|))
    ⟹  [zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)².

The error term `o(n^{α-1}(log n)²)` comes directly from the log²-weighted little-o circle
transfer `coeff_norm_isLittleO_atTop_of_delta_littleO_logSq_beta_gt_one`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

open AnalyticCombinatorics

theorem AnalyticCombinatorics.logSq_transfer_theorem_natural_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSqSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by sorry
