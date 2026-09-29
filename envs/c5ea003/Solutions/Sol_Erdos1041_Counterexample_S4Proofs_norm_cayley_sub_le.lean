-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.norm_cayley_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:24:18.148543+00:00
-- url     : https://prove2.me/submissions/33e28d24-5a3a-4236-bce3-8887a03ff740

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_cayley_den_ne_zero
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
noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution {x : ℝ} {w : ℂ} {M D T : ℝ} (hT : 0 ≤ T)
    (hA : |1 - w.re - w.im * x| ≤ M) (hB : |x + w.re * x - w.im| ≤ M)
    (hD : 0 < D) (hx : D ≤ 1 + x ^ 2) (hfin : 2 * M ^ 2 ≤ T ^ 2 * D) :
    ‖cayley x - w‖ ≤ T := by
  have hden := cayley_den_ne_zero x
  have hrw : cayley x - w
      = ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I))
        / (1 - (x : ℂ) * Complex.I) := by
    rw [cayley]; field_simp
  have hd2 : ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 = 1 + x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hn2 : ‖(1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)‖ ^ 2
      = (1 - w.re - w.im * x) ^ 2 + (x + w.re * x - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdpos : 0 < ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ := norm_pos_iff.mpr hden
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hAsq : (1 - w.re - w.im * x) ^ 2 ≤ M ^ 2 := by nlinarith [hA'.1, hA'.2]
  have hBsq : (x + w.re * x - w.im) ^ 2 ≤ M ^ 2 := by nlinarith [hB'.1, hB'.2]
  have hscale : T ^ 2 * D ≤ T ^ 2 * (1 + x ^ 2) :=
    mul_le_mul_of_nonneg_left hx (sq_nonneg T)
  rw [hrw, norm_div, div_le_iff₀ hdpos]
  have hkey : ‖(1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)‖ ^ 2
      ≤ (T * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖) ^ 2 := by
    have h1 : (T * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖) ^ 2
        = T ^ 2 * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 := by ring
    rw [h1, hd2, hn2]
    linarith [hAsq, hBsq, hfin, hscale]
  nlinarith [hkey, norm_nonneg ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)),
    mul_nonneg hT hdpos.le]
