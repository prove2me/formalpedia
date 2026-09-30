-- Prove2me | solution 1 for lean_workbook_plus_52299
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:52:27.7381+00:00
-- url     : https://prove2.me/submissions/ea42801e-7d57-400d-80a1-bb41696688ed

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem bounded_ratio_mono (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    s/(1+s) ≤ t/(1+t) := by
  have ht : 0 ≤ t := hs.trans hst
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hst]

theorem bounded_ratio_subadditive (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u+v)/(1+u+v) ≤ u/(1+u)+v/(1+v) := by
  have huv : 0 ≤ u*v := mul_nonneg hu hv
  rw [add_div]
  apply add_le_add
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [huv]
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [huv]

theorem solution (x y : ℝ) :
    abs (x-y)/(1+abs (x-y)) ≤
      (abs (2*x+y)+abs (x+2*y))/(1+abs (2*x+y)+abs (x+2*y)) := by
  have he : (2*x+y)-(x+2*y) = x-y := by ring
  have hab : |x-y| ≤ |2*x+y|+|x+2*y| := by
    simpa only [he] using abs_sub (2*x+y) (x+2*y)
  simpa only [add_assoc] using bounded_ratio_mono _ _ (abs_nonneg _) hab

theorem full_source_chain (x y : ℝ) :
    abs (x-y)/(1+abs (x-y)) ≤
      abs (2*x+y)/(1+abs (2*x+y))+abs (x+2*y)/(1+abs (x+2*y)) :=
  (solution x y).trans (bounded_ratio_subadditive _ _ (abs_nonneg _) (abs_nonneg _))
