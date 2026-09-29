-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlitBase_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:29:34.777182+00:00
-- url     : https://prove2.me/submissions/b2ed1739-ea55-4f87-bfbb-69ac2e5210a9

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlit_iff_norm
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
open Topology

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (v : ℂ) (hv : v ≠ 0) :
    IsOpen (bottleneckSlitBase v) := by
  let K : Set ℂ := {w | ‖v‖ ≤ ‖w‖ ∧
    w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ))}
  have hK : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_eq continuous_id (by fun_prop))
  have heq : bottleneckSlitBase v = {w : ℂ | ‖w‖ < 1} ∩ Kᶜ := by
    ext w
    change (‖w‖ < 1 ∧ w ∉ bottleneckSlit v) ↔
      ‖w‖ < 1 ∧ ¬(‖v‖ ≤ ‖w‖ ∧ w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)))
    rw [bottleneckSlit_iff_norm v w hv]
    tauto
  rw [heq]
  exact (isOpen_lt continuous_norm continuous_const).inter hK.isOpen_compl
