-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.pow_sub_one_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:19:18.360078+00:00
-- url     : https://prove2.me/submissions/12d8776b-11d4-48f9-8530-8dae73bf4b70

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_normalised_geom_prefix_le
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

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

namespace ErdosProblems.Erdos257.DyadicShellSynchronisation
end ErdosProblems.Erdos257.DyadicShellSynchronisation

/-!
# The finite estimate (S)

All three regimes refer to the actual modular atom, not abstract error terms.
The complete-orbit argument is in OrbitBound. The dyadic reciprocal-tail bound
is reused from the compiled WeightedSupportAveraging module. This file proves
no-wrap and transition bounds and then assembles the uniform finite estimate.
NOT COMPILED in this return.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.DyadicShellSynchronisation
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.DyadicShellSynchronisation
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution {B : ℝ} (hB : 1 < B)
    (n d : ℕ) (hd : 0 < d) (hnd : n ≤ d) :
    (B ^ n - 1) / (B ^ d - 1) ≤ (n : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hden : 0 < B ^ d - 1 := kernel_den_pos hB hd
  have h := normalised_geom_prefix_le hB.le n d hnd
  -- Mathlib/Algebra/Field/GeomSum.lean: geom_sum_eq, opened at the pin.
  rw [geom_sum_eq hB.ne', geom_sum_eq hB.ne'] at h
  have hmul := mul_le_mul_of_nonneg_right h hgap.le
  have hscaled : (d : ℝ) * (B ^ n - 1) ≤ (n : ℝ) * (B ^ d - 1) := by
    convert hmul using 1 <;> field_simp [hgap.ne']
  exact (div_le_div_iff₀ hden hdR).2 (by nlinarith only [hscaled])
end
