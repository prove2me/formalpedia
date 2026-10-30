-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogTransfer
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogTransfer
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:14.740066+00:00
-- url     : https://prove2.me/theorems/dc59e6cb-08be-442e-a94b-9650b6768026
-- title:
--   Analytic single-logarithmic singularity
-- statement:
--   The complex function z maps to (1-z)^(-alpha)(-Log(1-z)), using principal complex powers and logarithms.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogTransfer.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
import Mathlib
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
# Flajolet–Odlyzko transfer with a logarithmic factor (strong-remainder form)

The algebraic transfer theorem (`transfer_theorem_re_alpha_gt_one`) handles `f(z) ~ C(1−z)^{−α}`.
This file adds the *logarithmic* singularity transfer

  `f(z) ~ C (1−z)^{−α} log(1/(1−z))   ⟹   [zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`,

in the **strong-remainder** form: the residual is assumed `o(|1−z|^{−α})` (one log factor stronger
than the natural `o(|1−z|^{−α} log)`).  This lets the *existing* algebraic Darboux descent
(`coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one`) supply the coefficient error
`o(n^{α−1}) = o(n^{α−1} log n)`, with no new contour estimate.  The model coefficient asymptotic is the
banked `logSingularityCoeff_isEquivalent`.

The analytic faithfulness of the model `logSingularityFun α = (1−z)^{−α}·(−log(1−z))` (its
`HasFPowerSeriesAt` = `logSingularityGF α`, and delta-domain analyticity) is carried here as explicit
hypotheses; it is discharged separately (`LogTransferBranch`).
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The logarithmic-singularity model function `(1−z)^{−α} · (−log(1−z))`. -/
noncomputable def logSingularityFun (α : ℂ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z))


