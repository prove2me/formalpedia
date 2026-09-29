-- Prove2me | Theorems.Thm_lean_workbook_plus_13489
-- name    : lean_workbook_plus_13489
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/75d568a7-ea4b-40f3-b38c-d441db782efd
-- statement:
--   For $ a, b > 0$ and $ n \ge 2$ , prove that $ (a+b)^{n} > a^{n} + b^{n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13489 (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 2 ≤ n) : (a + b) ^ n > a ^ n + b ^ n   :=  by sorry
