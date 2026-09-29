-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.fract_block_natR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:08:34.378985+00:00
-- url     : https://prove2.me/submissions/d439cea5-614e-42f5-89a3-15fa85a60741

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperShortCapR9
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Definitions.Def_ErdosProblems_Erdos1049_G02WeightedBlocksR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_reciprocal_block_iff
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

/-! Literal thirteen-block supplier: the complement degree has quadratic rate. -/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n l : ℕ) (hl : 1 ≤ l) (u v : ℝ)
    (hu : 0 < u) (huv : u < v) (hv : v ≤ 1) :
    (u ≤ Int.fract ((n : ℝ)/l) ∧ Int.fract ((n : ℝ)/l) < v) ↔
      ∃ k ∈ range n, (n : ℝ)/((k : ℝ)+v) < l ∧
        (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+u) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  constructor
  · intro hx
    have hf0 : 0 ≤ ⌊(n : ℝ)/l⌋ := Int.floor_nonneg.mpr (div_nonneg hn0 hl0.le)
    let k : ℕ := ⌊(n : ℝ)/l⌋.toNat
    have hkZ : (k : ℤ) = ⌊(n : ℝ)/l⌋ := Int.toNat_of_nonneg hf0
    have hkR : (k : ℝ) = (⌊(n : ℝ)/l⌋ : ℝ) := by exact_mod_cast hkZ
    have hb : (k : ℝ)+u ≤ (n : ℝ)/l ∧ (n : ℝ)/l < (k : ℝ)+v := by
      change u ≤ (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) ∧
        (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) < v at hx
      rw [hkR]
      constructor <;> linarith [hx.1, hx.2]
    have hdiv : (n : ℝ)/l ≤ n := by
      apply (div_le_iff₀ hl0).2
      nlinarith
    have hkn : k < n := by exact_mod_cast (show (k : ℝ) < n by linarith [hb.1])
    refine ⟨k, mem_range.mpr hkn, ?_⟩
    exact (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).1 hb
  · rintro ⟨k, hk, hb⟩
    have hh := (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).2 hb
    have hf : ⌊(n : ℝ)/l⌋ = (k : ℤ) := Int.floor_eq_iff.mpr
      ⟨by push_cast; linarith [hh.1], by push_cast; linarith [hh.2]⟩
    change u ≤ (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) ∧
      (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) < v
    rw [hf]
    push_cast
    constructor <;> linarith [hh.1, hh.2]
