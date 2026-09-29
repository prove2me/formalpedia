-- Prove2me | Theorems.Thm_lean_workbook_plus_76840
-- name    : lean_workbook_plus_76840
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/119f56e4-cab1-4d2f-abb3-098b6afcb567
-- statement:
--   $(x+1)(y+1)\ge 0\Longrightarrow xy\ge -x-y-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76840 (x y : ℝ) (h : (x + 1) * (y + 1) ≥ 0) :
  x * y ≥ -x - y - 1   :=  by sorry
