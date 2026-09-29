-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlitBase_starConvex
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:30:09.613796+00:00
-- url     : https://prove2.me/submissions/d891517a-1711-474c-9979-1f7d2b04b836

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlit_iff_norm
import Theorems.Thm_Erdos1041_Counterexample_zero_not_mem_bottleneckSlit
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
    StarConvex ℝ (0 : ℂ) (bottleneckSlitBase v) := by
  intro w hw a b ha hb hab
  have hbone : b ≤ 1 := by linarith
  have hnorm : ‖b • w‖ = b * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg hb]
  have hnormle : ‖b • w‖ ≤ ‖w‖ := by
    rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_right hbone (norm_nonneg w)]
  have hbw : b • w ∈ bottleneckSlitBase v := by
    refine ⟨hnormle.trans_lt hw.1, ?_⟩
    intro hslit
    have hbzero : b ≠ 0 := by
      intro hz
      subst b
      exact zero_not_mem_bottleneckSlit v hv (by simpa using hslit)
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hbzero
    have hsmul (z : ℂ) : b • z = (b : ℂ) * z := Complex.real_smul
    obtain ⟨hlower, -, hdir⟩ := (bottleneckSlit_iff_norm v (b • w) hv).mp hslit
    have hwdir : w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)) := by
      apply mul_left_cancel₀ hbC
      calc
        (b : ℂ) * w = b • w := (hsmul w).symm
        _ = (‖b • w‖ : ℂ) * (v / (‖v‖ : ℂ)) := hdir
        _ = (b : ℂ) * ((‖w‖ : ℂ) * (v / (‖v‖ : ℂ))) := by
          rw [hnorm, Complex.ofReal_mul]
          ring
    exact hw.2 ((bottleneckSlit_iff_norm v w hv).mpr
      ⟨hlower.trans hnormle, hw.1, hwdir⟩)
  have hcollapse : a • (0 : ℂ) + b • w = b • w := by
    rw [show a • (0 : ℂ) = (a : ℂ) * 0 from Complex.real_smul, mul_zero, zero_add]
  rw [hcollapse]
  exact hbw
