-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.norm_ge_one_of_Q_re
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:37:12.767081+00:00
-- url     : https://prove2.me/submissions/162fc644-4adc-41b5-94a8-7a915f3bf2ee

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
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





theorem rho_pos : 0 < (ρ : ℝ) := by norm_num [ρ, s]
theorem eps_pos : 0 < (ε : ℝ) := by norm_num [ε, s]










theorem f_eval_scaled (w : ℂ) :
    f.eval ((ρ : ℂ) * (ε : ℂ) * w) =
      (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
  simp only [f, Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  unfold a b c ε
  push_cast <;> ring

theorem f_re_scaled (w : ℂ) :
    (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re =
      (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (Q.eval w).re) := by
  rw [f_eval_scaled]
  have hr : (ρ : ℂ) = ((ρ : ℝ) : ℂ) := by norm_cast
  have he : (ε : ℂ) = ((ε : ℝ) : ℂ) := by norm_cast
  rw [hr, he, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im]
  ring

theorem real_threshold :
    (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (-K_hi)) ≤ -1 := by
  norm_num [ρ, ε, s, K_hi]
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (w : ℂ) (hw : K_hi + (Q.eval w).re ≤ 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  have hq : (Q.eval w).re ≤ -K_hi := by linarith
  have he : 0 ≤ (ε : ℝ) ^ 7 := pow_nonneg eps_pos.le 7
  have hr : 0 ≤ (ρ : ℝ) ^ 7 := pow_nonneg rho_pos.le 7
  have hf : (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re ≤ -1 := by
    rw [f_re_scaled]
    have h1 : (ε : ℝ) ^ 7 * (Q.eval w).re ≤ (ε : ℝ) ^ 7 * (-K_hi) :=
      mul_le_mul_of_nonneg_left hq he
    have h2 : (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (Q.eval w).re)
        ≤ (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (-K_hi)) := by
      refine mul_le_mul_of_nonneg_left ?_ hr
      linarith
    linarith [real_threshold]
  have habs := Complex.abs_re_le_norm (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
  rw [abs_of_nonpos (by linarith : (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re ≤ 0)] at habs
  linarith
