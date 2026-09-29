-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.totient_constant_le_halfR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:23:50.194794+00:00
-- url     : https://prove2.me/submissions/d510d19e-ffbd-4f21-8eb6-43ec2de26585

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_constant_reciprocal_zetaR16
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# G02 arithmetic suppliers: the summatory totient with an explicit error

Proves |Σ_{d≤y} φ(d) - (3/π²)y²| ≤ 2y(1 + log(1+y)) for every real y ≥ 0.
The definitions below are genuine totient/Möbius sums. No asymptotic
supplier is assumed as an axiom, typeclass field, or theorem premise.
-/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
theorem solution : totientConstantR16 ≤ 1 / 2 := by
  have hz : (1 : ℝ) ≤ zetaTwoR16 := by
    have h := hasSum_zeta_two.summable.le_tsum 1
      (fun d _ => by positivity)
    simpa [zetaTwoR16, hasSum_zeta_two.tsum_eq] using h
  rw [totient_constant_reciprocal_zetaR16]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * zetaTwoR16)
    (by norm_num : (0 : ℝ) < 2)).2
  nlinarith
