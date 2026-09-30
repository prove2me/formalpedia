-- Prove2me | solution 1 for polynomial_grid_continuous_extension
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:04:46.004189+00:00
-- url     : https://prove2.me/submissions/1609d40e-92fe-45e8-9786-e28e034bc4c1

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Polynomial

theorem solution :
    ¬ (∀ {b : ℕ} (Q : Polynomial ℝ) {d : ℕ},
      Q.natDegree ≤ d →
      (∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) →
      2 * d ^ 2 ≤ b →
      ∀ x : ℝ, 0 ≤ x → x ≤ (b : ℝ) → |Q.eval x| ≤ 1) := by
  intro h
  let Q : Polynomial ℝ := 1 + C (1 / 28) * (X - X ^ 2)
  have hdeg : Q.natDegree ≤ 2 := by
    dsimp [Q]
    compute_degree
  have hgrid : ∀ t : ℕ, t ≤ 8 → |Q.eval (t : ℝ)| ≤ 1 := by
    intro t ht
    interval_cases t <;> norm_num [Q]
  have hbad := @h 8 Q 2 hdeg hgrid (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  norm_num [Q] at hbad

#print axioms solution
