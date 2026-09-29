-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.weighted_indicator_blocksR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:25:14.447204+00:00
-- url     : https://prove2.me/submissions/4b97c177-21e8-4465-89de-86865995135d

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
import Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_bounds
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_reciprocal_block_iff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_fract_block_natR16
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















lemma sourceIntervals_separatedR16 :
    ∀ uv ∈ sourceIntervals, ∀ wx ∈ sourceIntervals,
      uv = wx ∨ uv.2 ≤ wx.1 ∨ wx.2 ≤ uv.1 := by
  simp only [sourceIntervals, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  norm_num

lemma sourceIntervals_uniqueR16 (uv wx : ℚ × ℚ)
    (huv : uv ∈ sourceIntervals) (hwx : wx ∈ sourceIntervals)
    (x : ℝ) (hx : (uv.1 : ℝ) ≤ x ∧ x < (uv.2 : ℝ))
    (hy : (wx.1 : ℝ) ≤ x ∧ x < (wx.2 : ℝ)) : uv = wx := by
  rcases sourceIntervals_separatedR16 uv huv wx hwx with h | h | h
  · exact h
  · have h' : (uv.2 : ℝ) ≤ wx.1 := by exact_mod_cast h
    exfalso; linarith [hx.1, hx.2, hy.1, hy.2]
  · have h' : (wx.2 : ℝ) ≤ uv.1 := by exact_mod_cast h
    exfalso; linarith [hx.1, hx.2, hy.1, hy.2]





















lemma block_index_uniqueR16 (n l k j : ℕ) (hl : 1 ≤ l)
    (u v a b : ℝ) (hu : 0 < u) (huv : u < v) (hv : v ≤ 1)
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hk : (n : ℝ)/((k : ℝ)+v) < l ∧ (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+u))
    (hj : (n : ℝ)/((j : ℝ)+b) < l ∧ (l : ℝ) ≤ (n : ℝ)/((j : ℝ)+a)) : k = j := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have h1 := (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).2 hk
  have h2 := (reciprocal_block_iff n l j a b hl0 (Nat.cast_nonneg _) ha hab).2 hj
  have hf1 : ⌊(n : ℝ)/l⌋ = (k : ℤ) := Int.floor_eq_iff.mpr
    ⟨by push_cast; linarith [h1.1], by push_cast; linarith [h1.2]⟩
  have hf2 : ⌊(n : ℝ)/l⌋ = (j : ℤ) := Int.floor_eq_iff.mpr
    ⟨by push_cast; linarith [h2.1], by push_cast; linarith [h2.2]⟩
  omega
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
theorem solution (n l : ℕ) (hl : 1 ≤ l) :
    (if ∃ uv ∈ sourceIntervals,
        (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
          Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
      then (l.totient : ℝ) else 0) =
    ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
      if (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) < l ∧
        (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
      then (l.totient : ℝ) else 0 := by
  classical
  by_cases hex : ∃ uv ∈ sourceIntervals,
      (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
        Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
  · rw [if_pos hex]
    obtain ⟨uv, huv, hx⟩ := hex
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    obtain ⟨k, hk, hblock⟩ := (fract_block_natR16 n l hl _ _ hu huv' hv).1 hx
    symm
    calc
      _ = ∑ j ∈ range n,
          if (n : ℝ)/((j : ℝ)+(uv.2 : ℝ)) < l ∧
            (l : ℝ) ≤ (n : ℝ)/((j : ℝ)+(uv.1 : ℝ))
          then (l.totient : ℝ) else 0 := by
        apply sum_eq_single uv
        · intro wx hwx hne
          apply sum_eq_zero
          intro j hj
          apply if_neg
          intro hb
          obtain ⟨ha, hab, hb1⟩ := sourceIntervals_bounds wx hwx
          have hxx := (fract_block_natR16 n l hl _ _ ha hab hb1).2 ⟨j, hj, hb⟩
          exact hne (sourceIntervals_uniqueR16 wx uv hwx huv _ hxx hx)
        · intro hn; exact (hn huv).elim
      _ = l.totient := by
        rw [sum_eq_single k]
        · simp [hblock]
        · intro j hj hjk
          apply if_neg
          intro hb
          exact hjk (block_index_uniqueR16 n l j k hl _ _ _ _ hu huv' hv hu huv' hv hb hblock)
        · intro hn; exact (hn hk).elim
  · rw [if_neg hex]
    symm
    apply sum_eq_zero
    intro uv huv
    apply sum_eq_zero
    intro k hk
    apply if_neg
    intro hb
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    exact hex ⟨uv, huv, (fract_block_natR16 n l hl _ _ hu huv' hv).2 ⟨k, hk, hb⟩⟩
