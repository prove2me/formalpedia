-- Prove2me | Theorems.Thm_lean_workbook_plus_358
-- name    : lean_workbook_plus_358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/aaeadb54-fff7-47e2-b879-7cb0c1e9a954
-- statement:
--   Let $ x$ be an integer. What is the smallest possible value of $ |2x - 7| + |2x - 9| + |2x - 11| + |2x - 13| + |2x - 15|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_358 (x : ℤ) : 13 ≤ |2*x - 7| + |2*x - 9| + |2*x - 11| + |2*x - 13| + |2*x - 15|   :=  by sorry
