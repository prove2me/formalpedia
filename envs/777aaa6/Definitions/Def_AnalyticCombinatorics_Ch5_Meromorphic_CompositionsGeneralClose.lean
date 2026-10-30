-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneralClose
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneralClose
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:33:18.390996+00:00
-- url     : https://prove2.me/theorems/ffb5751a-9767-4cca-8424-7455827fe7a8
-- title:
--   Finite part series and denominator polynomial
-- statement:
--   partSeriesℂ S is the formal series sum of X^s over S. denominatorPolynomial S is the complex polynomial 1-sum X^s. Separate theorems derive the asymptotic for actual composition counts under positivity, at least two allowed sizes, and gcd one; no asymptotic is a definition of the counts.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/CompositionsGeneralClose.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Closing the general finite-part composition family

This file supplies the formal OGF bridge, the derivative nonvanishing input, and the
dominant-pole decomposition needed by `CompositionsGeneral`.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral
namespace Close

/-- The finite part series `∑_{s∈S} X^s`. -/
def partSeriesℂ (S : Finset ℕ) : PowerSeries ℂ :=
  ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s

/-- The denominator polynomial `1 - P_S(X)`. -/
def denominatorPolynomial (S : Finset ℕ) : Polynomial ℂ :=
  1 - ∑ s ∈ S, Polynomial.X ^ s

end Close
end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics


