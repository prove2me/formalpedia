-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.sum_kernelWeight_gcdOrbit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:05:46.552698+00:00
-- url     : https://prove2.me/submissions/ee1d046d-c970-487f-b317-a37f6fd5d4a6

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

namespace Erdos257PeriodNoncollapse.TotientTailPeriodKiller
end Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-!
# Real-base complete-orbit bookkeeping

Generalises the *repaired existing* binary proof in
Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean, lines 153--280,
without changing its finite permutation argument. Unlike the binary result,
this applies at B=2^α for α arbitrarily close to zero.
NOT COMPILED in this return. No premise is an irrationality conclusion.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB : 1 < B)
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    (∑ k ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((k + 1) * L)) =
      1 / (B ^ Nat.gcd L d - 1) := by
  classical
  let g := Nat.gcd L d
  let q := L / g
  let h := d / g
  -- Mathlib/Data/Nat/GCD/Basic.lean: gcd positivity, cancellation and coprime quotient.
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hgL : g ∣ L := Nat.gcd_dvd_left L d
  have hgd : g ∣ d := Nat.gcd_dvd_right L d
  have hLfac : g * q = L := Nat.mul_div_cancel' hgL
  have hdfac : g * h = d := Nat.mul_div_cancel' hgd
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hcop : Nat.Coprime q h := Nat.coprime_div_gcd_div_gcd hg
  let e : Fin h → Fin h := fun j =>
    ⟨((j : ℕ) + 1) * q % h, Nat.mod_lt _ hh⟩
  have heinj : Function.Injective e := by
    intro a b hab
    have habval : (e a : ℕ) = (e b : ℕ) := congrArg Fin.val hab
    have hmod : ((a : ℕ) + 1) * q ≡ ((b : ℕ) + 1) * q [MOD h] := habval
    -- Mathlib/Data/Nat/ModEq.lean: cancel_right_of_coprime,
    -- add_left_cancel', eq_of_lt_of_lt (pinned source opened).
    have hcancel : (a : ℕ) + 1 ≡ (b : ℕ) + 1 [MOD h] :=
      Nat.ModEq.cancel_right_of_coprime hcop.symm.gcd_eq_one hmod
    have habmod : (a : ℕ) ≡ (b : ℕ) [MOD h] := by
      have hcancel' : 1 + (a : ℕ) ≡ 1 + (b : ℕ) [MOD h] := by
        simpa only [add_comm] using hcancel
      exact hcancel'.add_left_cancel' 1
    exact Fin.ext (habmod.eq_of_lt_of_lt a.isLt b.isLt)
  -- Mathlib/Data/Fintype/Card.lean: Finite.surjective_of_injective.
  have hebij : Function.Bijective e :=
    ⟨heinj, Finite.surjective_of_injective heinj⟩
  have hresidue : ∀ j : Fin h,
      (((j : ℕ) + 1) * L) % d = g * (e j : ℕ) := by
    intro j
    rw [← hLfac, ← hdfac]
    rw [show ((j : ℕ) + 1) * (g * q) = g * (((j : ℕ) + 1) * q) by ring]
    rw [Nat.mul_mod_mul_left]
  have hsumPerm :
      (∑ j : Fin h, B ^ ((((j : ℕ) + 1) * L) % d)) =
        ∑ r : Fin h, B ^ (g * (r : ℕ)) := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean: Fintype.sum_bijective.
    apply Fintype.sum_bijective e hebij
    intro j
    rw [hresidue]
  have hpowg : B ^ g ≠ 1 := ne_of_gt (one_lt_pow₀ hB hg.ne')
  have hdenD : B ^ d - 1 ≠ 0 := ne_of_gt (kernel_den_pos hB hd)
  have hdenG : B ^ g - 1 ≠ 0 := sub_ne_zero.mpr hpowg
  calc
    (∑ k ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((k + 1) * L)) =
        (∑ j : Fin h, B ^ ((((j : ℕ) + 1) * L) % d)) / (B ^ d - 1) := by
      -- Mathlib/Algebra/BigOperators/Fin.lean: Fin.sum_univ_eq_sum_range.
      rw [show d / Nat.gcd L d = h from rfl, ← Fin.sum_univ_eq_sum_range]
      simp only [kernelWeight, Finset.sum_div]
    _ = (∑ r : Fin h, B ^ (g * (r : ℕ))) / (B ^ d - 1) := by rw [hsumPerm]
    _ = (∑ r ∈ Finset.range h, (B ^ g) ^ r) / (B ^ d - 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply congrArg (fun z : ℝ => z / (B ^ d - 1))
      -- Mathlib/Data/Fintype/BigOperators.lean: Fintype.sum_congr.
      apply Fintype.sum_congr
      intro r
      rw [pow_mul]
    _ = ((B ^ g) ^ h - 1) / (B ^ g - 1) / (B ^ d - 1) := by
      -- Mathlib/Algebra/Field/GeomSum.lean: geom_sum_eq.
      rw [geom_sum_eq hpowg]
    _ = 1 / (B ^ Nat.gcd L d - 1) := by
      change ((B ^ g) ^ h - 1) / (B ^ g - 1) / (B ^ d - 1) = 1 / (B ^ g - 1)
      rw [← pow_mul, hdfac]
      field_simp [hdenD, hdenG]
end
