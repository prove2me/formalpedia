-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_rate_irrationality_unconditional
-- name    : ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T01:01:45.152613+00:00
-- url     : https://prove2.me/theorems/51fbd303-588d-4586-9bbc-f5813513b52c
-- title:
--   Cubic-rate irrationality for zero-indexed positive integer sequences
-- statement:
--   Let a be a strictly increasing sequence of positive integers indexed from zero. If n³(aₙ²/aₙ₊₁ − (1 + 3/n)) tends to zero and the reciprocal series has sum S, then S is irrational. This is the unconditional Lean theorem for the cubic-rate subclass; it does not settle the unrestricted Erdős Problem 243. The paper's one-based statement uses a separate finite-prefix argument.
--
--   **Where to inspect the proof.** The `:= by sorry` on this page is Prove2Me's challenge placeholder, not the accepted proof. The accepted Solution is under **View graph → Solutions & Sketches**, which asks signed-out readers to sign in. The [public proof packet](https://github.com/wcook04/plectis-erdos/blob/cea5dbbb6331dceefbbf026d29d24043293dfecf/docs/research-commons/PROVE2ME_CUBIC_243_PACKET.md) prints the byte-exact accepted Solution, links the pinned Lean source and paper, and shows the proved every-tail consequence. The unrestricted Erdős #243 problem remains open.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L67-L77
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110
--   Paper cubic-rate theorem and index bridge: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L740-L778

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


open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20

open ErdosProblems.Erdos243.PaperCompleteR21

theorem ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by sorry
