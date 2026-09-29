-- Prove2me | Theorems.Thm_lean_workbook_plus_60809
-- name    : lean_workbook_plus_60809
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b8198c4f-9f59-4967-b21a-2bb96b3ac458
-- statement:
--   Let $z=f(x,y)=ax+by+c$ defines a plane with $z=f(1, 2) = a+2b+c=-1$ , then $c=-1-a-2b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60809 (a b c : ℝ) : a + 2 * b + c = -1 → c = -1 - a - 2 * b   :=  by sorry
