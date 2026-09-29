-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.shiftQuad_spec
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:20:49.828266+00:00
-- url     : https://prove2.me/submissions/65300472-e992-46cc-99d6-c54bf593da9b

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
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcc : (Polynomial.derivative p).eval cc = 0) (z : ℂ) :
    (shiftQuad p cc).eval z * z ^ 2 = p.eval (cc + z) - p.eval cc := by
  set g : Polynomial ℂ := p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)
    with hg
  have hgeval : ∀ y : ℂ, g.eval y = p.eval (cc + y) - p.eval cc := by
    intro y
    simp [hg, Polynomial.eval_comp, add_comm]
  have hc0 : g.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hgeval]
    simp
  have hderiv : Polynomial.derivative g
      = (Polynomial.derivative p).comp (Polynomial.X + Polynomial.C cc) := by
    simp [hg, Polynomial.derivative_comp]
  have hc1 : g.coeff 1 = 0 := by
    have h0 : (Polynomial.derivative g).coeff 0 = g.coeff 1 := by
      simp [Polynomial.coeff_derivative]
    have h1 : (Polynomial.derivative g).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hderiv]
      simp [Polynomial.eval_comp, hcc]
    rw [← h0, h1]
  have hdvd : (Polynomial.X ^ 2 : Polynomial ℂ) ∣ g := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact hc0
    · exact hc1
  have hmonic : (Polynomial.X ^ 2 : Polynomial ℂ).Monic := Polynomial.monic_X_pow 2
  have hmod : g %ₘ (Polynomial.X ^ 2) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hmul : (Polynomial.X ^ 2 : Polynomial ℂ) * (g /ₘ (Polynomial.X ^ 2)) = g := by
    have h := Polynomial.modByMonic_add_div g (Polynomial.X ^ 2 : Polynomial ℂ)
    rw [hmod, zero_add] at h
    exact h
  have : (shiftQuad p cc) = g /ₘ (Polynomial.X ^ 2) := rfl
  rw [this]
  have := congrArg (fun q : Polynomial ℂ => q.eval z) hmul
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at this
  rw [hgeval] at this
  linear_combination this
