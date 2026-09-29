-- Prove2me | Theorems.Thm_lean_workbook_plus_25829
-- name    : lean_workbook_plus_25829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/902406e4-b053-4a44-bcec-5abe15be52ff
-- statement:
--   Let $ a,b,c\geq 0$ . Prove that $ \sum a^2(a-b)(a-c)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25829 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^2 * (a - b) * (a - c) + b^2 * (b - a) * (b - c) + c^2 * (c - a) * (c - b) ≥ 0   :=  by sorry
