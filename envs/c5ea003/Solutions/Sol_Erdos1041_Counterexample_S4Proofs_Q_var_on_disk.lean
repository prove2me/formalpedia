-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Q_var_on_disk
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:11:32.32778+00:00
-- url     : https://prove2.me/submissions/5df8431c-9ec3-47a3-a4f3-2449ec53b821

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_taylor
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
theorem solution {v : ℂ} {rr g1 g2 g3 g4 g5 g6 g7 : ℝ} (hr : 0 ≤ rr)
    (h1 : ‖qT1 v‖ ≤ g1) (h2 : ‖qT2 v‖ ≤ g2) (h3 : ‖qT3 v‖ ≤ g3) (h4 : ‖qT4 v‖ ≤ g4)
    (h5 : ‖qT5 v‖ ≤ g5) (h6 : ‖qT6 v‖ ≤ g6) (h7 : ‖qT7‖ ≤ g7) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr →
      ‖Q.eval w - qT0 v‖
        ≤ g1 * rr + g2 * rr ^ 2 + g3 * rr ^ 3 + g4 * rr ^ 4 + g5 * rr ^ 5 + g6 * rr ^ 6
          + g7 * rr ^ 7 := by
  intro w hw
  have hq := Q_taylor v (w - v)
  rw [show v + (w - v) = w by ring] at hq
  have hrew : Q.eval w - qT0 v
      = qT1 v * (w - v) + qT2 v * (w - v) ^ 2 + qT3 v * (w - v) ^ 3 + qT4 v * (w - v) ^ 4
        + qT5 v * (w - v) ^ 5 + qT6 v * (w - v) ^ 6 + qT7 * (w - v) ^ 7 := by
    rw [hq]; ring
  have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn → ‖dd * (w - v) ^ k‖ ≤ nn * rr ^ k := by
    intro dd nn k hdd
    rw [norm_mul, norm_pow]
    exact mul_le_mul hdd (pow_le_pow_left₀ (norm_nonneg _) hw k) (by positivity)
      (le_trans (norm_nonneg _) hdd)
  have t1 := hb (qT1 v) g1 1 h1
  have t2 := hb (qT2 v) g2 2 h2
  have t3 := hb (qT3 v) g3 3 h3
  have t4 := hb (qT4 v) g4 4 h4
  have t5 := hb (qT5 v) g5 5 h5
  have t6 := hb (qT6 v) g6 6 h6
  have t7 := hb qT7 g7 7 h7
  rw [hrew]
  set X1 := qT1 v * (w - v)
  set X2 := qT2 v * (w - v) ^ 2
  set X3 := qT3 v * (w - v) ^ 3
  set X4 := qT4 v * (w - v) ^ 4
  set X5 := qT5 v * (w - v) ^ 5
  set X6 := qT6 v * (w - v) ^ 6
  set X7 := qT7 * (w - v) ^ 7
  have H2 : ‖X1 + X2‖ ≤ ‖X1‖ + ‖X2‖ := norm_add_le _ _
  have H3 : ‖X1 + X2 + X3‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ :=
    le_trans (norm_add_le _ _) (add_le_add H2 le_rfl)
  have H4 : ‖X1 + X2 + X3 + X4‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ :=
    le_trans (norm_add_le _ _) (add_le_add H3 le_rfl)
  have H5 : ‖X1 + X2 + X3 + X4 + X5‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ :=
    le_trans (norm_add_le _ _) (add_le_add H4 le_rfl)
  have H6 : ‖X1 + X2 + X3 + X4 + X5 + X6‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ + ‖X6‖ :=
    le_trans (norm_add_le _ _) (add_le_add H5 le_rfl)
  have H7 : ‖X1 + X2 + X3 + X4 + X5 + X6 + X7‖
      ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ + ‖X6‖ + ‖X7‖ :=
    le_trans (norm_add_le _ _) (add_le_add H6 le_rfl)
  simp only [pow_one] at t1
  linarith [H7, t1, t2, t3, t4, t5, t6, t7]
