-- Prove2me | Theorems.Thm_lean_workbook_plus_69021
-- name    : lean_workbook_plus_69021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5a5e8154-9e53-450f-ad69-11b69aa9ff51
-- statement:
--   Prove: if $xv=yu$, then $x(y+v)=y(x+u)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69021 (x y u v : ℝ) (h : x * v = y * u) :
  x * (y + v) = y * (x + u)   :=  by sorry
