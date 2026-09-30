-- Prove2me | solution 1 for lean_workbook_plus_64700
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:41.316081+00:00
-- url     : https://prove2.me/submissions/dc184885-9954-4347-85fa-76cf667135c5

import Mathlib.Analysis.Complex.Basic

lemma aux_pos (x y z : ℝ) (hx : x + y + z > 0) (hy : x*y + x*z + y*z > 0) (hz : x*y*z > 0) : x > 0 := by
  by_contra h
  push_neg at h
  have hyz : y * z < 0 := by
    by_contra h2
    push_neg at h2
    nlinarith [mul_nonneg h2 (neg_nonneg.mpr h)]
  have hs : y + z > 0 := by linarith
  nlinarith [mul_nonneg (neg_nonneg.mpr h) (le_of_lt hs)]

theorem solution (x y z : ℝ) (hx : x + y + z > 0) (hy : x*y + x*z + y*z > 0) (hz : x*y*z > 0) : x > 0 ∧ y > 0 ∧ z > 0 := by
  refine ⟨aux_pos x y z hx hy hz, ?_, ?_⟩
  · exact aux_pos y x z (by linarith) (by linarith) (by linarith)
  · exact aux_pos z x y (by linarith) (by linarith) (by linarith)
