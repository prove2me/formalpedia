-- Prove2me | solution 1 for lean_workbook_plus_54261
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:10.052809+00:00
-- url     : https://prove2.me/submissions/8dc7e4b3-a451-4960-8846-08923f1e301d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : a + b + c > 0) (hb : a * b + b * c + c * a > 0) (hc : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0 := by
  have pos (u v w : ℝ) (hs : 0 < u+v+w) (hp : 0 < u*v+v*w+w*u) (ht : 0 < u*v*w) : 0 < u := by
    by_contra hn
    have hu : u ≤ 0 := le_of_not_gt hn
    have hneg := mul_nonpos_of_nonpos_of_nonneg hu hs.le
    have hf : 0 < u^2-u*(u+v+w)+(u*v+v*w+w*u) := by nlinarith [sq_nonneg u]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hu hf.le
    nlinarith
  refine ⟨pos a b c ha hb hc, ?_, ?_⟩
  · apply pos b c a <;> nlinarith
  · apply pos c a b <;> nlinarith
