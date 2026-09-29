-- Prove2me | Theorems.Thm_lean_workbook_plus_15538
-- name    : lean_workbook_plus_15538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/aa392cd8-e5b8-4000-ac04-c22a6e13730c
-- statement:
--   $(m_x-b)^2+(m_y-c)^2=(n_x-b)^2+(n_y-c)^2\iff (m_x-n_x)(m_x+n_x-2b)+(m_y-n_y)(m_y+n_y-2c)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15538  (b c m_x m_y n_x n_y: ℝ) :
  (m_x - b)^2 + (m_y - c)^2 = (n_x - b)^2 + (n_y - c)^2 ↔ (m_x - n_x) * (m_x + n_x - 2 * b) + (m_y - n_y) * (m_y + n_y - 2 * c) = 0   :=  by sorry
