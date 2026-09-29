-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Q_eval_expanded
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:08:07.151072+00:00
-- url     : https://prove2.me/submissions/40bc1983-4b3e-45aa-a648-8dcba219aa87

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
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
    Q.eval w = w ^ 7 + a * w ^ 3 + b * w ^ 2 + c * w
      - (s : ℂ) ^ 2 * conj a * w ^ 4
      - (s : ℂ) ^ 6 * conj b * w ^ 5
      - (s : ℂ) ^ 10 * conj c * w ^ 6 := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, a, b, c]
  push_cast
  ring
