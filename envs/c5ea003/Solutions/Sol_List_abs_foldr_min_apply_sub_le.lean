-- Prove2me | solution 1 for List.abs_foldr_min_apply_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:44:17.453766+00:00
-- url     : https://prove2.me/submissions/c6ded8ae-30f4-4cd4-8102-cd32bbdc1836

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

open List

theorem solution (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ min (f x) s) r -
        l.foldr (fun f s ↦ min (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))
