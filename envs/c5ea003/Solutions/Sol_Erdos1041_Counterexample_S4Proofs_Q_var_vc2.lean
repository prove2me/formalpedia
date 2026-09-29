-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Q_var_vc2
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:17:19.92328+00:00
-- url     : https://prove2.me/submissions/b729ffc0-8419-42d7-9738-ed266213b74c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_var_on_disk
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT7_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT1_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT2_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT3_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT4_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT5_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT6_vc2_bound
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
theorem solution : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc2‖ ≤ (95050744432731764040616235381367 / 500000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc2) (by norm_num)
    qT1_vc2_bound qT2_vc2_bound qT3_vc2_bound qT4_vc2_bound qT5_vc2_bound
    qT6_vc2_bound qT7_bound w hw) (by norm_num)
