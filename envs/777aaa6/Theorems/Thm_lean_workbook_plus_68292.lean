-- Prove2me | Theorems.Thm_lean_workbook_plus_68292
-- name    : lean_workbook_plus_68292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/059430b7-c975-47e5-af03-deff33f62910
-- statement:
--   $(a+b+c)^2\le 3(a^2+b^2+c^2)\Leftrightarrow (a-b)^2+(b-c)^2+(c-a)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68292 (a b c : ℝ) : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) ↔ (a-b)^2+(b-c)^2+(c-a)^2 ≥ 0   :=  by sorry
