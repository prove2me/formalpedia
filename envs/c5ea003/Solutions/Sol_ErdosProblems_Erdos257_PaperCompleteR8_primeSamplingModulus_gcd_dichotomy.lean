-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.primeSamplingModulus_gcd_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:03:53.251028+00:00
-- url     : https://prove2.me/submissions/9655cd29-0121-4edd-b893-d3a37d2fe7d9

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSetPart_dvd
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSamplingModulus_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSetPart_dvd_product_pow
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















/-- Every selected prime's H-th power divides the sampling modulus. -/
theorem prime_pow_dvd_sampling (L : ℕ) (P : Finset ℕ) (H p : ℕ) (hp : p ∈ P) :
    p ^ H ∣ primeSamplingModulus L P H := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem id hp
  have hd : p ^ H ∣ P.prod id ^ H := by
    rw [hc, mul_pow]
    exact dvd_mul_right _ _
  exact dvd_mul_of_dvd_right hd L
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution {L : ℕ} (hL : 0 < L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (H a : ℕ) (ha : 0 < a) :
    primeSetPart P a ∣ Nat.gcd (primeSamplingModulus L P H) a ∨
      2 ^ H ≤ Nat.gcd (primeSamplingModulus L P H) a := by
  classical
  by_cases hsmall : ∀ p ∈ P, a.factorization p ≤ H
  · apply Or.inl
    exact Nat.dvd_gcd
      (dvd_mul_of_dvd_right (primeSetPart_dvd_product_pow P a H hsmall) L)
      (primeSetPart_dvd P ha)
  · push_neg at hsmall
    obtain ⟨p, hp, hlarge⟩ := hsmall
    have hpa : p ^ H ∣ a :=
      ((hP p hp).pow_dvd_iff_le_factorization ha.ne').mpr hlarge.le
    have hpg : p ^ H ∣ Nat.gcd (primeSamplingModulus L P H) a :=
      Nat.dvd_gcd (prime_pow_dvd_sampling L P H p hp) hpa
    have hQ : 0 < primeSamplingModulus L P H := primeSamplingModulus_pos hL P hP H
    have hg : 0 < Nat.gcd (primeSamplingModulus L P H) a :=
      Nat.gcd_pos_of_pos_left a hQ
    exact Or.inr ((Nat.pow_le_pow_left (hP p hp).two_le H).trans
      (Nat.le_of_dvd hg hpg))
end
