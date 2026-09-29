-- Prove2me | Theorems.Thm_lean_workbook_plus_21312
-- name    : lean_workbook_plus_21312
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d673dcbc-2633-42e7-a2d0-f49ea8f58ddb
-- statement:
--   Prove that $(a-b)(b-c)(c-a) = (b-c)(c-a)+(c-a)(a-b)+(a-b)(b-c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21312 : ∀ a b c : ℤ, (a - b) * (b - c) * (c - a) = (b - c) * (c - a) + (c - a) * (a - b) + (a - b) * (b - c)   :=  by sorry
