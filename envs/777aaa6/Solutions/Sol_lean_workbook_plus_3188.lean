-- Prove2me | solution 1 for lean_workbook_plus_3188
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:01.640711+00:00
-- url     : https://prove2.me/submissions/2f4e3ec2-2ed4-4245-a2f5-197a7c60aaf7

import Mathlib.Analysis.Complex.Basic

theorem solution    (x y z w : ℝ)
    (h : x^3 + y^3 + z^3 + w^3 = 4) :
    ∃ μ : ℝ, μ^3 = 4 / (x^3 + y^3 + z^3 + w^3) := by
  refine ⟨1, ?_⟩
  rw [h]
  norm_num
