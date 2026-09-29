-- Prove2me | Theorems.Thm_lean_workbook_plus_69261
-- name    : lean_workbook_plus_69261
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e83752ef-9527-4319-a98b-3f9daccc36d1
-- statement:
--   (a+b+c)^2\ge 9 \implies a+b+c\ge 3 for positive $a,b,c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69261 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 ≥ 9 → a + b + c ≥ 3   :=  by sorry
