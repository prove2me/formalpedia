-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.actual_weighted_blocksR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:21:04.937147+00:00
-- url     : https://prove2.me/submissions/224ad28a-fa62-422f-b6a8-e1c18fe68e82

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_bounds
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_reciprocal_totient_block
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_weighted_totient_indicator
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_reciprocal_endpoint_capR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_weighted_indicator_blocksR16
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









































lemma finite_prefix_eq_totientR16 (N : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hxN : x ≤ N) : (finiteTotientPrefix N x : ℝ) = totientPrefixR16 x := by
  classical
  have hfloor : ⌊x⌋₊ ≤ N := by
    have h := Nat.floor_mono hxN
    simpa using h
  have hset : (Icc 1 N).filter (fun l : ℕ => (l : ℝ) ≤ x) = Icc 1 ⌊x⌋₊ := by
    ext l
    simp only [mem_filter, mem_Icc, ← Nat.le_floor_iff hx]
    omega
  unfold finiteTotientPrefix totientPrefixR16
  push_cast
  rw [← sum_filter, hset]
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
theorem solution (n : ℕ) :
    (actualWeightedTotientSum n : ℝ) =
      ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
        (totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
          totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ)))) := by
  classical
  rw [actual_weighted_totient_indicator]
  push_cast
  have he : (∑ l ∈ Icc 1 (15*n),
      if ∃ uv ∈ sourceIntervals,
        (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
          Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
      then (l.totient : ℝ) else 0) =
      ∑ l ∈ Icc 1 (15*n), ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
        if (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) < l ∧
          (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
        then (l.totient : ℝ) else 0 := by
    apply sum_congr rfl
    intro l hl
    exact weighted_indicator_blocksR16 n l (mem_Icc.mp hl).1
  rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro uv huv
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hcap := reciprocal_endpoint_capR16 n k uv huv
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (actual_reciprocal_totient_block (15*n) n k uv.1 uv.2
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hu huv')
  push_cast at h
  rw [finite_prefix_eq_totientR16 _ _ (hcap.1.trans hcap.2.1)
      (by push_cast; nlinarith [hcap.2.2, Nat.cast_nonneg (α := ℝ) n]),
    finite_prefix_eq_totientR16 _ _ hcap.1
      (by push_cast; nlinarith [hcap.2.1, hcap.2.2, Nat.cast_nonneg (α := ℝ) n])] at h
  exact h
