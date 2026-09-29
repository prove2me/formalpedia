-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.one_sub_normSq_f_rho_eps
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:19:43.551791+00:00
-- url     : https://prove2.me/submissions/553d5262-517b-44e4-b36b-8523aa3d797a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_f_eval_rho_eps
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
theorem normSq_rho_pow : Complex.normSq ((ρ : ℂ) ^ 7) = (ρ : ℝ) ^ 14 := by
  rw [map_pow]
  simp only [Complex.normSq_apply, Complex.ratCast_re, Complex.ratCast_im]
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
    1 - Complex.normSq (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
      = 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by
  have he : ((ε : ℂ)) ^ 7 = ((((ε : ℝ)) ^ 7 : ℝ) : ℂ) := by push_cast; ring
  have h2 : Complex.normSq (-1 + ((((ε : ℝ)) ^ 7 : ℝ) : ℂ) * Q.eval w)
      = 1 - 2 * (ε : ℝ) ^ 7 * (Q.eval w).re
        + ((ε : ℝ) ^ 7) ^ 2 * Complex.normSq (Q.eval w) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [f_eval_rho_eps, Complex.normSq_mul, normSq_rho_pow, he, h2]
  have hr : ((ρ : ℝ)) ≠ 0 := ne_of_gt rho_pos
  have hepsr : ((ε : ℝ)) ≠ 0 := ne_of_gt eps_pos
  unfold Hs K0
  field_simp
  ring
