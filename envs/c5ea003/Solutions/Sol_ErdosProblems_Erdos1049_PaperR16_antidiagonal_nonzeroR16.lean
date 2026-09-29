-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.antidiagonal_nonzeroR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:11:54.738692+00:00
-- url     : https://prove2.me/submissions/3e2dec41-c0b1-4331-a3d2-418a2fa2d0de

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
theorem solution {n : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ n.divisorsAntidiagonal) : x.1 ≠ 0 ∧ x.2 ≠ 0 := by
  have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hn := (Nat.mem_divisorsAntidiagonal.mp hx).2
  constructor
  · intro h
    apply hn
    rw [← hp, h, zero_mul]
  · intro h
    apply hn
    rw [← hp, h, mul_zero]
