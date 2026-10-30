-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalanGeneralThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_FussCatalanGeneralThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:45:46.421441+00:00
-- url     : https://prove2.me/theorems/829a4d72-88e4-4f0c-8d20-0cb6b3b0e23a
-- title:
--   Fuss–Catalan radii, main terms and correction polynomials
-- statement:
--   For fixed p, the radius is (p-1)^(p-1)/p^p; the real main term multiplies its negative-n power by n^(-3/2) and the leading constant. Explicit Stirling correction, first and second relative constants define the quadratic approximation in 1/n. The real Raney coefficient uses the binomial numerator and denominator (p-1)n+1. Private inverse-Stirling ratios, rational prefactors and quadratic polynomials record the expansion arithmetic.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/FussCatalanGeneralThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalan
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order Fuss-Catalan coefficient asymptotic, fixed general arity

This file proves the relative third-order asymptotic for the closed form

`1 / ((p - 1)n + 1) * binom (pn) n`.

The only analytic input is the third-order Stirling-sequence expansion already
proved in `CayleyThirdOrder`, applied at `n`, `(p - 1)n`, and `pn`.
-/

set_option maxHeartbeats 1600000

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS

noncomputable section

def fussCatalanGeneralRho (p : ℕ) : ℝ :=
  (((p - 1 : ℕ) : ℝ) ^ (p - 1)) / ((p : ℝ) ^ p)

def fussCatalanGeneralLeadingConstant (p : ℕ) : ℝ :=
  fussCatalanConst p

def fussCatalanGeneralMainTermBase (p n : ℕ) : ℝ :=
  fussCatalanGeneralLeadingConstant p * fussCatalanBase p ^ n *
    ((n : ℝ) ^ (-(3 / 2 : ℝ)))

def fussCatalanGeneralMainTerm (p n : ℕ) : ℝ :=
  (fussCatalanGeneralRho p) ^ (-(n : ℝ)) *
    ((n : ℝ) ^ (-(3 / 2 : ℝ))) *
      fussCatalanGeneralLeadingConstant p

def fussCatalanGeneralStirlingC (p : ℕ) : ℝ :=
  -((1 + (p : ℝ) * ((p - 1 : ℕ) : ℝ)) /
      (12 * (p : ℝ) * ((p - 1 : ℕ) : ℝ)))

def fussCatalanGeneralC1 (p : ℕ) : ℝ :=
  -(((p : ℝ) ^ 2 + 11 * (p : ℝ) + 1) /
      (12 * (p : ℝ) * ((p - 1 : ℕ) : ℝ)))

def fussCatalanGeneralC2 (p : ℕ) : ℝ :=
  let q : ℝ := ((p - 1 : ℕ) : ℝ)
  1 / q ^ 2 - fussCatalanGeneralStirlingC p / q +
    (fussCatalanGeneralStirlingC p) ^ 2 / 2

def fussCatalanGeneralThirdApprox (p n : ℕ) : ℝ :=
  1 + fussCatalanGeneralC1 p * (n : ℝ)⁻¹ +
    fussCatalanGeneralC2 p * ((n : ℝ)⁻¹) ^ 2

def fussCatalanRaneyCoeff (p n : ℕ) : ℝ :=
  (1 / ((((p - 1) * n + 1 : ℕ) : ℝ))) *
    (((Nat.choose (p * n) n : ℕ) : ℝ))

def stirlingInvRatio (n : ℕ) : ℝ :=
  Real.sqrt Real.pi / Stirling.stirlingSeq n

def stirlingInvRatioApprox (a n : ℕ) : ℝ :=
  1 - (1 / (12 * (a : ℝ))) * (n : ℝ)⁻¹ +
    (1 / (288 * (a : ℝ) ^ 2)) * ((n : ℝ)⁻¹) ^ 2

def stirlingLinear (a : ℕ) : ℝ :=
  -(1 / (12 * (a : ℝ)))

def stirlingQuadratic (a : ℕ) : ℝ :=
  1 / (288 * (a : ℝ) ^ 2)

def stirlingProductApprox (p n : ℕ) : ℝ :=
  1 + fussCatalanGeneralStirlingC p * (n : ℝ)⁻¹ +
    ((fussCatalanGeneralStirlingC p) ^ 2 / 2) * ((n : ℝ)⁻¹) ^ 2

def rationalPrefactorApprox (q n : ℕ) : ℝ :=
  1 - (1 / (q : ℝ)) * (n : ℝ)⁻¹ +
    (1 / ((q : ℝ) ^ 2)) * ((n : ℝ)⁻¹) ^ 2

def rationalPrefactor (q n : ℕ) : ℝ :=
  (((q * n : ℕ) : ℝ)) / (((q * n + 1 : ℕ) : ℝ))

def poly2 (a b : ℝ) (n : ℕ) : ℝ :=
  1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2

end

end AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS


