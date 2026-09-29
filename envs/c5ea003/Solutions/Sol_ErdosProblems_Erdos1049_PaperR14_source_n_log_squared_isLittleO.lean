-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR14.source_n_log_squared_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:45:34.820323+00:00
-- url     : https://prove2.me/submissions/ec5eba23-14b9-40f8-927d-3b365a1d599a

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
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
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

namespace PaperR13
end PaperR13

/-!
# Subquadratic coefficient heights of the actual cancelled source pair

Proves the cancelled pair's coefficient heights have zero quadratic log rate.

This file uses the actual `sourceU` and `sourceV`, the all-index coefficient
bound from R13, and the unchanged maximum/l1 height definitions of the papers.
The analytic limit and the degree+1 transport are proved here, not assumed.
The intentionally conservative numerical envelope is 5000*n*(1+log(n+2))^2.
-/

namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR11 PaperR12 PaperR13
open scoped BigOperators Topology
end ErdosProblems.Erdos1049.PaperR14

set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR11 PaperR12 PaperR13
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR14 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR13 in
theorem solution :
    (fun n : ℕ => (n : ℝ) * sourceLogScale n ^ 2) =o[atTop] PaperR9.sqScale := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl : (fun x : ℝ => Real.log x ^ (2 : ℕ)) =o[atTop] (fun x : ℝ => x) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ) (s := 1) (by norm_num))
  have hseq := hl.comp_tendsto ht
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hseq.def (show 0 < ε / 12 by positivity),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with n hn hln hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := hnR.trans' zero_le_one
  have hx0 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (Real.log ((n : ℝ) + 2))), abs_of_nonneg hx0] at hn hln
  have hscale : sourceLogScale n ^ 2 ≤ 4 * Real.log ((n : ℝ) + 2) ^ 2 := by
    unfold sourceLogScale
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 4 * n by positivity)
  have hlast : 4 * (n : ℝ) * (ε / 12 * ((n : ℝ) + 2)) ≤ ε * (n : ℝ) ^ 2 := by
    have hx : (n : ℝ) + 2 ≤ 3 * (n : ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_left hx (show 0 ≤ 4 * (n : ℝ) * (ε / 12) by positivity)
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hscale hn0
  simpa only [PaperR9.sqScale, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hn0 (sq_nonneg _)), abs_of_nonneg (sq_nonneg (n : ℝ))] using
      hfirst.trans (by nlinarith)
