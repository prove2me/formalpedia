-- Prove2me | solution 1 for lean_workbook_plus_28434
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:56.870743+00:00
-- url     : https://prove2.me/submissions/6ac28dd0-30e7-4f39-9b74-2e29ee0e79b1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℕ) (a1 : a 0 = 3)
    (a_rec : ∀ n, a (n + 1) = a n + 5 + 4 * 2 ^ n + 3 ^ (n + 1) + 2 * 4 ^ n + 5 ^ n) :
    ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  have hclosed (n : ℕ) : 12 * a n + 41 =
      60 * n + 48 * 2 ^ n + 18 * 3 ^ n + 8 * 4 ^ n + 3 * 5 ^ n := by
    induction n with
    | zero => norm_num [a1]
    | succ n ih =>
        rw [a_rec]
        simp only [pow_succ]
        ring_nf at ih ⊢
        omega
  refine ⟨fun n =>
    (60 * n + 48 * 2 ^ n + 18 * 3 ^ n + 8 * 4 ^ n + 3 * 5 ^ n - 41) / 12, ?_⟩
  intro n
  dsimp only
  have h := hclosed n
  omega

#print axioms solution
