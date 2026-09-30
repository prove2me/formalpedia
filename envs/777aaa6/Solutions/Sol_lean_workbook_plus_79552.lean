-- Prove2me | solution 1 for lean_workbook_plus_79552
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:54.084717+00:00
-- url     : https://prove2.me/submissions/b17d724f-703b-4945-bcdf-f91b1c9f9a90

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem radical_transition (t : ℝ) (ht : 0 ≤ t) :
    (1 + 4 * ((t ^ 2 - 1) / 24) + Real.sqrt (1 + 24 * ((t ^ 2 - 1) / 24))) / 16 =
      (((t + 3) / 2) ^ 2 - 1) / 24 := by
  rw [show 1 + 24 * ((t ^ 2 - 1) / 24) = t ^ 2 by ring, Real.sqrt_sq ht]
  ring

theorem solution (a : ℕ → ℚ) (a1 : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16) :
    ∃ f : ℕ → ℚ, ∀ n, a n = f n := by
  let q (n : ℕ) : ℚ := 3 + 2 / 2 ^ n
  have hq (n : ℕ) : q (n + 1) = (q n + 3) / 2 := by
    dsimp [q]
    rw [pow_succ]
    field_simp
    ring
  refine ⟨fun n => (q n ^ 2 - 1) / 24, ?_⟩
  intro n
  induction n with
  | zero => norm_num [q, a1]
  | succ n ih =>
      dsimp only at ih ⊢
      apply Rat.cast_injective (α := ℝ)
      push_cast
      have hr := a_rec n
      rw [ih] at hr
      push_cast at hr
      rw [radical_transition _ (by dsimp [q]; positivity)] at hr
      rw [hq n]
      push_cast
      exact hr

#print axioms solution
