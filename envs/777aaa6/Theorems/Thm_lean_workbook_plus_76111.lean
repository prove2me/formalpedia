-- Prove2me | Theorems.Thm_lean_workbook_plus_76111
-- name    : lean_workbook_plus_76111
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a622d5f9-d2ab-4cdd-95b7-279c9662d401
-- statement:
--   This problem requires some casework, because the first movie could be a documentary.\n1. If the first movie is not a documentary: there are $29$ choices for the first non-documentary movie, then $39\\times38\\times37$ ways for the remaining three movies. In total, there are $1,590,186$ ways.\n2. If the first movie is a documentary: there are $3$ choices for the first movie, then $40\\times39\\times38$ ways for the other three movies. There are $177,840$ ways for this case.\nAdding the two cases together, we have a total of $\boxed{1,768,026}$ ways.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76111 (29*39*38*37) + (3*40*39*38) = 1768026   :=  by sorry
