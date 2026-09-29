-- Prove2me | Theorems.Thm_lean_workbook_plus_77870
-- name    : lean_workbook_plus_77870
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a2ff2223-7025-4701-8c10-e3cd07de5760
-- statement:
--   Prove that \((a + b + c)^2 - 3(a + b + c) + 6 \ge 2(ab + bc + ca)\), given \(abc = 1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77870 : a * b * c = 1 → (a + b + c) ^ 2 - 3 * (a + b + c) + 6 ≥ 2 * (a * b + b * c + a * c)   :=  by sorry
