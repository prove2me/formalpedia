-- Prove2me | Theorems.Thm_lean_workbook_plus_43373
-- name    : lean_workbook_plus_43373
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a7921f21-a79b-45ef-aceb-0b1dae1bf450
-- statement:
--   Given the inequalities: $\frac 23 m_b+\frac 13 m_c > \frac 12 c,\ \frac 23 m_c+\frac 13 m_b >\frac 12 b$,\nprove that 2(m_b+m_c) > b+c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43373 (b c m_b m_c : ℝ) : (2 / 3 * m_b + 1 / 3 * m_c > 1 / 2 * c ∧ 2 / 3 * m_c + 1 / 3 * m_b > 1 / 2 * b) → 2 * (m_b + m_c) > b + c   :=  by sorry
