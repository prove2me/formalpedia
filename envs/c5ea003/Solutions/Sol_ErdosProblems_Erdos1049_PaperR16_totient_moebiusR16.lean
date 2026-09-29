-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.totient_moebiusR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:26:37.832985+00:00
-- url     : https://prove2.me/submissions/441ae1f7-2cbe-4a1a-ae52-60a8f6d8117e

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
theorem solution (r : ℕ) (hr : 0 < r) :
    (r.totient : ℝ) = ∑ x ∈ r.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℝ) * (x.2 : ℝ) := by
  symm
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d.totient : ℝ)) (g := fun d => (d : ℝ))).mp
      (fun n _ => by exact_mod_cast Nat.sum_totient n) r hr
