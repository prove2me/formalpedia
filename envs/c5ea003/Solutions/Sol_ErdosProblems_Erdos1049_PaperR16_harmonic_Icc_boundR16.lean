-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.harmonic_Icc_boundR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:10:20.210457+00:00
-- url     : https://prove2.me/submissions/4c65bb98-d5bd-4b7c-916f-89329ac1fdd9

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
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
theorem solution (m : ℕ) :
    (∑ d ∈ Icc 1 m, (1 : ℝ)/(d : ℝ)) ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h
