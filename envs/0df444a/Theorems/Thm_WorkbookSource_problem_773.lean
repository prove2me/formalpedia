-- Prove2me | Theorems.Thm_WorkbookSource_problem_773
-- name    : WorkbookSource.problem_773
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:08.624615+00:00
-- url     : https://prove2.me/theorems/725ff0b8-65cc-41eb-8f3b-62f4f48d9fce
-- title:
--   A three-variable product inequality
-- statement:
--   For all real $a,b,c$, $$(a^2+1)(b^2+1)(c^2+1)\ge(abc-1)^2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_773` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_773; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_773 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2  :=  by sorry
