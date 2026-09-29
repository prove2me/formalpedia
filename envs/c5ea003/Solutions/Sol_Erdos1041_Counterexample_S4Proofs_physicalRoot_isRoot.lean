-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.physicalRoot_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:22:04.332425+00:00
-- url     : https://prove2.me/submissions/f6fd0781-d8ca-4d96-81f1-2249505e13dc

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
/-- The exact Gaussian-rational identity behind the whole root argument.
Proved by clearing the nonvanishing Cayley denominator; no approximation. -/
theorem cayley_identity (x : ℝ) :
    (1 - (x : ℂ) * Complex.I) ^ 7 * F.eval (cayley x) =
      2 * Complex.I * (cayleyH x : ℂ) := by
  have hden := cayley_den_ne_zero x
  rw [F_eval, conj_a, conj_b, conj_c]
  unfold cayley cayleyH a b c
  push_cast
  field_simp
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, pow_succ] <;> ring
theorem realRoot_zero (j : Fin 7) : cayleyH (realRoot j) = 0 :=
  (Classical.choose_spec (exists_cayley_root j)).2
theorem cayley_realRoot_isRoot (j : Fin 7) : F.IsRoot (cayley (realRoot j)) := by
  have h := cayley_identity (realRoot j)
  rw [realRoot_zero] at h
  simp only [Complex.ofReal_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (cayley_den_ne_zero _))
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution (j : Fin 7) : f.IsRoot (physicalRoot j) := by
  have h : f.eval ((ρ : ℂ) * cayley (realRoot j)) = 0 := by
    rw [f_eval_scale, cayley_realRoot_isRoot, mul_zero]
  exact h
