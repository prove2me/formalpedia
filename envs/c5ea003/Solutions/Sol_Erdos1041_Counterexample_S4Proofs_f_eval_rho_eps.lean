-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.f_eval_rho_eps
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:18:14.516426+00:00
-- url     : https://prove2.me/submissions/3caea9d0-a804-40cc-910b-df94c0331432

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_eval_expanded
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
/-- Exact rescaling, without introducing a reciprocal polynomial. -/
theorem f_eval_scale (z : ℂ) :
    f.eval ((ρ : ℂ) * z) = (ρ : ℂ) ^ 7 * F.eval z := by
  simp only [f, F, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring
/-- `F` written out in the paper's form (paper (1.3)). -/
theorem F_eval (z : ℂ) :
    F.eval z = z ^ 7 - 1
      + (ε : ℂ) ^ 4 * (a * z ^ 3 - conj a * z ^ 4)
      + (ε : ℂ) ^ 5 * (b * z ^ 2 - conj b * z ^ 5)
      + (ε : ℂ) ^ 6 * (c * z - conj c * z ^ 6) := by
  simp only [F, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring
/-- The first exact scaling identity, paper (4.4). -/
theorem F_eval_eps (w : ℂ) :
    F.eval ((ε : ℂ) * w) = -1 + (ε : ℂ) ^ 7 * Q.eval w := by
  rw [Q_eval_expanded, F_eval]
  simp only [ε]
  push_cast
  ring
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution (w : ℂ) :
    f.eval ((ρ : ℂ) * (ε : ℂ) * w) =
      (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
  rw [mul_assoc, f_eval_scale, F_eval_eps]
