-- Prove2me | solution 1 for lean_workbook_plus_15538
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:53.292384+00:00
-- url     : https://prove2.me/submissions/38392486-1264-4bf9-88fa-892d6fa28719

import Mathlib.Analysis.Complex.Basic

theorem solution  (b c m_x m_y n_x n_y: ℝ) :
  (m_x - b)^2 + (m_y - c)^2 = (n_x - b)^2 + (n_y - c)^2 ↔ (m_x - n_x) * (m_x + n_x - 2 * b) + (m_y - n_y) * (m_y + n_y - 2 * c) = 0 := by
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h
