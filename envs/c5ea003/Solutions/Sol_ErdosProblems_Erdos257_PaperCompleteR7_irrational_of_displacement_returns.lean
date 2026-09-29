-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR7.irrational_of_displacement_returns
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:04.278995+00:00
-- url     : https://prove2.me/submissions/20fa895f-c5d0-4bcd-9f2d-91ec1c6772b9

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Definitions.Def_Erdos249257_GenericTailOrbitRigidity
import Definitions.Def_Erdos249257_GreedyAchievementSet
import Definitions.Def_Erdos249257_RationalSupportCarrySkeleton
import Definitions.Def_Erdos249257_ReciprocalSupportIrrationality
import Definitions.Def_Erdos249257_AllBaseReciprocalSupportIrrationality
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Theorems.Thm_Erdos249257_tsum_shiftedRadixSupportAtom_zero
import Theorems.Thm_ErdosProblems_Erdos257_irrational_erdosSupportSeries_of_radix_closeReturn
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Perfect

/-!
# Infinite displacement and the exact arithmetic consumer

Compiled R7 proof candidates against the supplied Lean 4.29.1 tree.
Unlike the already supplied finite rational tail-budget draft, this file
uses the actual infinite real support series. All summability hypotheses
needed to interchange infinite sums are proved from the existing library.

The arithmetic endgame reuses RadixCloseReturn's general
close-return consumer, translated into displacement notation. No reciprocal-
summability hypothesis is added or removed from that consumer. The ordinary
positive-cover and mixed-support arguments must still establish its analytic
input. No admission, new axiom, or parent claim is used.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7
open Erdos257PeriodNoncollapse Filter Set
end ErdosProblems.Erdos257.PaperCompleteR7

open Erdos257PeriodNoncollapse Filter Set
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR7 in
theorem solution (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ displacement b A N < ε) :
    Irrational (Erdos249257.erdosSupportSeries b A) := by
  apply irrational_erdosSupportSeries_of_radix_closeReturn b A hb hA
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := hreturn ε hε
  refine ⟨N, hN, ?_⟩
  rw [Erdos249257.tsum_shiftedRadixSupportAtom_zero]
  unfold displacement at hsmall
  linarith
end
