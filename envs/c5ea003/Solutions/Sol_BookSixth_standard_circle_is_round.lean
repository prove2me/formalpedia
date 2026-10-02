-- Prove2me | solution 1 for BookSixth.standard_circle_is_round
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T00:16:23.492006+00:00
-- url     : https://prove2.me/submissions/2b46196f-93af-404b-a4a4-24b8688d5dc5

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem solution (i : ℕ) : RoundCircle (standardCircle i) := by
  -- `standardCircle i` is `![3 * (i : ℝ) + Real.cos t, Real.sin t, 0]`, so the cosine
  -- multiplies the FIRST coordinate direction: `u = ![1, 0, 0]`, `v = ![0, 1, 0]`.
  have hu : (∑ k, (![1, 0, 0] : Space3) k * (![1, 0, 0] : Space3) k) = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  have hv : (∑ k, (![0, 1, 0] : Space3) k * (![0, 1, 0] : Space3) k) = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  have huv : (∑ k, (![1, 0, 0] : Space3) k * (![0, 1, 0] : Space3) k) = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  refine ⟨![3 * (i : ℝ), 0, 0], ![1, 0, 0], ![0, 1, 0], 1, by norm_num, hu, hv, huv, ?_⟩
  -- The goal is `standardCircle i = Set.range (...)`, a *set* equality, so `funext` cannot
  -- start on it. Unfold the left and rewrite the two parametrisation bodies into each other
  -- as *functions*; the goal then becomes `Set.range lhs = Set.range lhs` and `rw` closes it.
  -- This is the idiom of the accepted `roundness_compose_two_general_DISPROVED_c3575_ACCEPTED.lean`
  -- (its `have hf` / `rw [hf]`). `hf` is stated expanded-on-the-left so that `rw [hf]`
  -- rewrites the goal's right-hand body into its left-hand one.
  have hf : (fun t : ℝ => ![3 * (i : ℝ), 0, 0]
            + (1 * Real.cos t) • ![1, 0, 0] + (1 * Real.sin t) • ![0, 1, 0])
      = (fun t : ℝ => ![3 * (i : ℝ) + Real.cos t, Real.sin t, 0]) := by
    funext t
    funext j
    fin_cases j <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]
  rw [standardCircle, hf]
