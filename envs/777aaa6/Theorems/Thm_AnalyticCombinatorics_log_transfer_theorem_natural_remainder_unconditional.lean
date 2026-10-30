-- Prove2me | Theorems.Thm_AnalyticCombinatorics_log_transfer_theorem_natural_remainder_unconditional
-- name    : AnalyticCombinatorics.log_transfer_theorem_natural_remainder_unconditional
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:46:44.610993+00:00
-- url     : https://prove2.me/theorems/adfd0af6-03d2-4314-a7c8-1eeea856e491
-- title:
--   Logarithmic transfer with the natural remainder
-- statement:
--   Let $C\in\mathbb C\setminus\{0\}$, $R>1$, $0<\phi<\pi/2$. Let $f$ have the specified formal multilinear power series $p$ at $0$, and be analytic on a neighbourhood of every point of the source dented domain $\Delta(R,\phi)$ (`DeltaDomainArg`). All limits at $1$ below are taken within that domain. Write $L_\alpha(z)=(1-z)^{-\alpha}[-\log(1-z)]$, with the source complex powers and logarithm. Fix a real $\alpha>1$. Assume $$\frac{\lVert f(z)-CL_\alpha(z)\rVert\,|1-z|^\alpha}{[\log(1/|1-z|)]^{1}}\longrightarrow0.$$ Then $$p_n\sim C\,\frac{n^{\alpha-1}}{\Gamma(\alpha)}(\log n)^{1}.$$ The power-series, domain, nonzero-leading-coefficient and full weighted remainder assumptions are all retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogTransferNatural.lean#L116. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogTransfer
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Flajolet–Odlyzko logarithmic transfer — natural-remainder form

`LogTransfer.lean` proves the *strong-remainder* logarithmic transfer, whose residual
hypothesis is `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α})` (one log factor stronger
than the textbook statement).  This file removes that caveat: the **natural** residual

  `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α} · log(1/|1−z|))`

(encoded via `‖·‖·‖1−z‖^α / log(1/‖1−z‖) → 0`) still yields

  `[zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`.

The new analytic content is the log-weighted Hankel/Cauchy contour estimate
`coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one` (in `LittleOTransfer`),
which supplies the error term `o(n^{α−1} log n)` directly — no algebraic absorption.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

theorem AnalyticCombinatorics.log_transfer_theorem_natural_remainder_unconditional
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by sorry
