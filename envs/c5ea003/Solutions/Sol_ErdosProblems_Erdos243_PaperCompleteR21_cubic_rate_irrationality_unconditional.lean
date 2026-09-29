-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:49:58.991775+00:00
-- url     : https://prove2.me/submissions/449bff1d-cd0a-49c5-9233-0046a4527faf

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_CubicRateExclusionChain
import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_rate_irrationality
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_squareSpecialisation_holds
import Mathlib
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: the square-specialisation lemma and its consumers, unconditionally

`SquareSpecialisationDedekind.lean` proves the statement of `long243:res:squarespec`
(`paper/reasoning-parts/erdos243/core.tex`, lemma at line 303) from the simple pole of the
Dedekind zeta function, which is in Mathlib; the Chebotarev density theorem is not used.  This
file records it as `squareSpecialisation : SquareSpecialisation` and discharges the hypothesis
`hss : SquareSpecialisation` of the three downstream paper statements in
`CubicRateExclusionChain.lean`:

* `transport_square_unconditional` — `long243:res:transportsquare`;
* `cubic_exclusion_unconditional` — `long243:res:cubicexclusion`;
* `cubic_rate_irrationality_unconditional` — `res:cubicrate` and `long243:res:cubicrate`.

Each is the corresponding `CubicRateExclusionChain` theorem applied to `squareSpecialisation`,
with no hypothesis added.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20

/-- **`long243:res:squarespec`**, with no hypothesis: if `f ∈ ℚ[T]` is irreducible with root
`α`, `H (α) ≠ 0`, and for all but finitely many primes `ℓ` every root `r` of `f` modulo `ℓ` has
`H (r)` a nonzero square modulo `ℓ`, then `H (α)` is a square in `ℚ(α)`. -/
theorem squareSpecialisation : SquareSpecialisation :=
  squareSpecialisation_holds
end ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv :=
  cubic_rate_irrationality squareSpecialisation a ha hpos hrate Sv hS
