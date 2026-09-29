-- Prove2me | solution 1 for markov_unit
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T08:06:40.726937+00:00
-- url     : https://prove2.me/submissions/e5f50b71-b049-4f3b-9aef-6db7013ee7ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_markov_unit
import Theorems.Thm_bernstein_unit
import Theorems.Thm_markov_from_bernstein
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Polynomial

/-- Sketch: reduce `markov_unit` to `bernstein_unit` + `markov_from_bernstein`.
Route: A. Markov 1889. Step 1 (Bernstein): `(1-c²) Q'(c)² ≤ d²` on `[-1,1]`.
Step 2 (comparison to T'_d): any `p` of degree `< d` satisfying the Bernstein
bound satisfies `|p| ≤ d²` on `[-1,1]`. Apply Step 2 to `p := Q'`.
Degenerate case `d = 0`: `Q` is constant, `Q' = 0`. -/
theorem solution : markov_unit := by
  intro Q d hd h c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: Q is constant, Q' = 0.
    subst hd0
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hd
    have : Q.derivative = 0 := by
      have := Polynomial.natDegree_eq_zero.mp hQ0
      obtain ⟨a, ha⟩ := this
      rw [← ha, Polynomial.derivative_C]
    rw [this, Polynomial.eval_zero, abs_zero]
    norm_num
  · -- d ≥ 1: apply Bernstein + markov_from_bernstein.
    have hbern := bernstein_unit Q hd h
    have hdeg : Q.derivative.natDegree < d := by
      rcases Nat.eq_zero_or_pos Q.natDegree with hQ0 | hQpos
      · -- Q is constant, Q' = 0.
        have : Q.derivative = 0 := by
          have := Polynomial.natDegree_eq_zero.mp hQ0
          obtain ⟨a, ha⟩ := this
          rw [← ha, Polynomial.derivative_C]
        rw [this, Polynomial.natDegree_zero]
        exact hdpos
      · exact (Polynomial.natDegree_derivative_lt (Nat.pos_iff_ne_zero.mp hQpos)).trans_le hd
    exact markov_from_bernstein Q.derivative hdeg hbern c hc1 hc2
