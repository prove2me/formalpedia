-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_TransferSecondOrderGeneral
-- name    : AnalyticCombinatorics_Ch4_Analytic_TransferSecondOrderGeneral
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:02.638993+00:00
-- url     : https://prove2.me/theorems/ead04a1f-172a-47ce-9b16-cc3d6cf10001
-- title:
--   Finite shift corrections and rising products
-- statement:
--   The shift correction is the finite sum of alpha+j for j from0 to k-1; the rising product multiplies the corresponding a+j factors. These explicit finite operations describe derivative-induced shifts in second-order coefficient estimates.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/TransferSecondOrderGeneral.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
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
# General second-order transfer

This file extends the second-order two-term transfer theorem to real exponents
away from the poles `1, 0, -1, ...`.  The proof follows the k-fold derivative
descent used by the all-real little-o transfer theorem.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

def secondOrderShiftCorr (α : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (α + (j : ℝ))

def rising (a : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (a + (j : ℝ))

end


