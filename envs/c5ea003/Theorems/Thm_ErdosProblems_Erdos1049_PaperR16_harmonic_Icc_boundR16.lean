-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_harmonic_Icc_boundR16
-- name    : ErdosProblems.Erdos1049.PaperR16.harmonic_Icc_boundR16
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:10:11.155894+00:00
-- url     : https://prove2.me/theorems/5b179fbf-2e00-42a1-85ef-8f69761a1c67
-- title:
--   Harmonic icc bound r16
-- statement:
--   The harmonic sum over 1≤d≤m is at most 1+log m.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/G02ArithmeticR16.lean#L333-L338
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

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

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000

open ErdosProblems.Erdos1049.PaperR16

theorem ErdosProblems.Erdos1049.PaperR16.harmonic_Icc_boundR16 (m : ℕ) :
    (∑ d ∈ Icc 1 m, (1 : ℝ)/(d : ℝ)) ≤ 1 + Real.log m := by sorry
