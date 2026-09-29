-- Prove2me | Theorems.Thm_lean_workbook_plus_64233
-- name    : lean_workbook_plus_64233
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4147b0a0-2982-4a2f-a730-b90d9b8bf58b
-- statement:
--   Let $ a,\ b,\ c$ be positive real numbers such that $ a^2 + b^2 + c^2 = 1.$ Prove that $ bc + ca + ab \geq 3abc(b + c + a).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64233 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : a^2 + b^2 + c^2 = 1 → bc + ca + ab ≥ 3 * a * b * c * (b + c + a)   :=  by sorry
