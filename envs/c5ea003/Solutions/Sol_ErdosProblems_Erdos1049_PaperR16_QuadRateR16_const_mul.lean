-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.QuadRateR16.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:34:41.545961+00:00
-- url     : https://prove2.me/submissions/eb56265d-4902-478a-8ddf-bf4b5c97d18b

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_sqScale_nonneg
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_littleO_bound
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

namespace PaperR9
end PaperR9

/-! Quadratic-rate transport lemmas and strict-rate dominance for the source.
The V step follows from strict separation of the U and remainder rates. -/

namespace ErdosProblems.Erdos1049.PaperR16
open Filter Asymptotics
open PaperR9
open scoped Topology
set_option maxHeartbeats 2000000
end ErdosProblems.Erdos1049.PaperR16

open Filter Asymptotics
open PaperR9
open scoped Topology
set_option maxHeartbeats 2000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadRateR16 f a) (c : ℝ) :
    QuadRateR16 (fun n => c*f n) (c*a) := by
  apply IsLittleO.of_bound
  intro ε hε
  have hc : 0 < |c|+1 := by positivity
  filter_upwards [littleO_bound _ hf (ε/(|c|+1)) (div_pos hε hc)] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)]
  have he : c*f n-(c*a)*sqScale n = c*(f n-a*sqScale n) := by ring
  rw [he, abs_mul]
  have hb := mul_le_mul_of_nonneg_left hn (abs_nonneg c)
  have hεeq : (|c|+1)*(ε/(|c|+1)) = ε := by field_simp [hc.ne']
  have hratio : |c| * (ε/(|c|+1)) ≤ ε := by
    have ht := mul_le_mul_of_nonneg_right (show |c| ≤ |c|+1 by linarith)
      (div_nonneg hε.le hc.le)
    linarith
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hratio (sqScale_nonneg n)])
