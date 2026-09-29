-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.block_prefix_errorR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:29:54.068252+00:00
-- url     : https://prove2.me/submissions/286581ab-6375-4e4e-8739-9a3c4b42ac0d

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_reciprocal_endpoint_capR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_summatory_totient_errorR16
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
theorem solution (n k : ℕ) (uv : ℚ × ℚ) (huv : uv ∈ sourceIntervals) :
    |(totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
       totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ)))) -
      totientConstantR16 * (n : ℝ)^2 * blockKernelR16 uv.1 uv.2 k| ≤
      4 * (n : ℝ) * (1+Real.log (1+14*(n : ℝ))) *
        (1/((k : ℝ)+(uv.1 : ℝ))) := by
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hcap := reciprocal_endpoint_capR16 n k uv huv
  let x : ℝ := (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
  let y : ℝ := (n : ℝ)/((k : ℝ)+(uv.2 : ℝ))
  have hx0 : 0 ≤ x := hcap.1.trans hcap.2.1
  have hy0 : 0 ≤ y := hcap.1
  have hyx : y ≤ x := hcap.2.1
  have hxm : x ≤ 14*(n : ℝ) := hcap.2.2
  have hx := summatory_totient_errorR16 x hx0
  have hy := summatory_totient_errorR16 y hy0
  have hxlog : Real.log (1+x) ≤ Real.log (1+14*(n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hylog : Real.log (1+y) ≤ Real.log (1+14*(n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hxE : totientErrorR16 x ≤ 2*x*(1+Real.log (1+14*(n : ℝ))) := by
    unfold totientErrorR16
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hyE : totientErrorR16 y ≤ 2*x*(1+Real.log (1+14*(n : ℝ))) := by
    unfold totientErrorR16
    apply mul_le_mul
    · linarith
    · linarith
    · exact add_nonneg zero_le_one (Real.log_nonneg (by linarith))
    · positivity
  have he : (totientPrefixR16 x - totientPrefixR16 y) -
      totientConstantR16*(n : ℝ)^2*blockKernelR16 uv.1 uv.2 k =
      (totientPrefixR16 x - totientConstantR16*x^2) -
        (totientPrefixR16 y - totientConstantR16*y^2) := by
    dsimp [x, y, blockKernelR16]
    have hku : (k : ℝ)+(uv.1 : ℝ) ≠ 0 := (by positivity : 0 < (k : ℝ)+(uv.1 : ℝ)).ne'
    have hkv : (k : ℝ)+(uv.2 : ℝ) ≠ 0 :=
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : 0 < (k : ℝ)+(uv.2 : ℝ)).ne'
    field_simp [hku, hkv]
    <;> ring
  change |(totientPrefixR16 x-totientPrefixR16 y)-_| ≤ _
  rw [he]
  calc
    _ ≤ |totientPrefixR16 x-totientConstantR16*x^2| +
        |totientPrefixR16 y-totientConstantR16*y^2| := abs_sub _ _
    _ ≤ totientErrorR16 x + totientErrorR16 y := add_le_add hx hy
    _ ≤ 4*x*(1+Real.log (1+14*(n : ℝ))) := by linarith
    _ = _ := by dsimp [x]; ring
