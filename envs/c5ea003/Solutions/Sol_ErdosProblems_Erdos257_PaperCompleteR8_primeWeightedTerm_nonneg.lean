-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.primeWeightedTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:41:45.428677+00:00
-- url     : https://prove2.me/submissions/dcd00d5a-d314-43d2-a3dc-357664575886

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSetPart_dvd
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Tactic
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
# A logarithm-free prime-power sampling modulus

The actual weighted prime part is retained. For
Q = L (prod P)^H, either the complete P-part of a divides gcd(Q,a), or
that gcd is at least 2^H. This replaces floor-logarithm bookkeeping with
one uniform exponent, and is sufficient for the weighted analytic proof.

Pinned arithmetic APIs opened at the specified commit:
Mathlib/Data/Nat/Factorization/Basic.lean and Defs.lean;
Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean and Defs.lean.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7



theorem primeSetPart_pos (P : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    0 < primeSetPart P a := Nat.pos_of_dvd_of_pos (primeSetPart_dvd P ha) ha
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (a : ℕ) : 0 ≤ primeWeightedTerm b P a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [primeWeightedTerm, Nat.cast_zero, zero_mul, div_zero, le_refl]
  · have hh := primeSetPart_pos P ha
    have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (kernel_den_pos hbR hh).le)
end
