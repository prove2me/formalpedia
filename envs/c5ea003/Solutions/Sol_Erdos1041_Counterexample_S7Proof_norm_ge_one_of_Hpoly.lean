-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.norm_ge_one_of_Hpoly
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:38:54.143887+00:00
-- url     : https://prove2.me/submissions/ade498cb-98c7-4c31-975a-0de87352b190

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_norm_ge_one_of_Q_re
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

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

/-!
The namespace `S7Proof` keeps the barrier lemmas separate from the shared
definitions in `Defs.lean`.  These lemmas are consumed by
`InstanceBarriers.lean` and belong to the successfully checked counterexample
dependency chain.
-/
noncomputable section

open scoped ComplexConjugate

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000



























theorem conj_a : conj a = (A : ℂ) + (s : ℂ) * Complex.I := by
  simp only [a, map_sub, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_b : conj b = -(Complex.I * (B : ℂ)) + ((9 / 5 : ℚ) : ℂ) * (s : ℂ) := by
  simp only [b, map_add, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_c : conj c = -(Cconst : ℂ) + ((162 / 25 : ℚ) : ℂ) * (s : ℂ) * Complex.I := by
  simp only [c, map_sub, map_neg, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem Hpoly_eq (w : ℂ) : Hpoly w.re w.im = K_hi + (Q.eval w).re := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, conj_a, conj_b, conj_c]
  norm_num [Hpoly, K_hi, a, b, c, A, B, Cconst, t, s, pow_succ,
    Complex.mul_re, Complex.mul_im]
  all_goals ring
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (w : ℂ) (hw : Hpoly w.re w.im ≤ 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  apply norm_ge_one_of_Q_re
  simpa only [Hpoly_eq] using hw
