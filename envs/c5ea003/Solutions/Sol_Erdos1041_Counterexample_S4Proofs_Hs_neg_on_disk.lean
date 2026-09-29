-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_neg_on_disk
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:09:25.961287+00:00
-- url     : https://prove2.me/submissions/0db388c6-f19f-4f1d-bd98-42381857ba0c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pow7_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_K0_le
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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution {v : ℂ} {rr var reHi : ℝ}
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : (qT0 v).re ≤ reHi)
    (hneg : reHi + var + 1 / 10 ^ 11 < 0) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → Hs w < 0 := by
  intro w hw
  have hv := hvar w hw
  have hrele : (Q.eval w).re - (qT0 v).re ≤ var := by
    have := Complex.abs_re_le_norm (Q.eval w - qT0 v)
    simp only [Complex.sub_re] at this
    calc (Q.eval w).re - (qT0 v).re ≤ |(Q.eval w).re - (qT0 v).re| := le_abs_self _
      _ ≤ ‖Q.eval w - qT0 v‖ := this
      _ ≤ var := hv
  have hquad : 0 ≤ ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) :=
    mul_nonneg (by linarith [eps_pow7_pos]) (Complex.normSq_nonneg _)
  unfold Hs
  linarith [K0_le, hrele, hre, hneg, hquad]
