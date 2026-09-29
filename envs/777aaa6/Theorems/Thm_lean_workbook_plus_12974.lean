-- Prove2me | Theorems.Thm_lean_workbook_plus_12974
-- name    : lean_workbook_plus_12974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a97d91a3-6e47-485c-ae88-b7415e6f883f
-- statement:
--   $ \frac{a}{m_a}= \frac{b}{m_b}= \frac{c}{m_c} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12974 (a b c m_a m_b m_c : ℝ) : a / m_a = b / m_b ∧ b / m_b = c / m_c → a / m_a = c / m_c   :=  by sorry
