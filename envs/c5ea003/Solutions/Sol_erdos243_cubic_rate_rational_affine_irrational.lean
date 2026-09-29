-- Prove2me | solution 1 for erdos243_cubic_rate_rational_affine_irrational
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T13:46:07.131831+00:00
-- url     : https://prove2.me/submissions/c0f127c5-745e-4807-9e00-c2ebd01e37a5

import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_rate_irrationality_unconditional
import Mathlib.NumberTheory.Real.Irrational

noncomputable section

theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 *
        ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv)
    (r q : ℚ) (hr : r ≠ 0) :
    Irrational ((r : ℝ) * Sv + (q : ℝ)) := by
  have h : Irrational Sv :=
    ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
      a ha hpos hrate Sv hS
  exact (h.ratCast_mul hr).add_ratCast q
