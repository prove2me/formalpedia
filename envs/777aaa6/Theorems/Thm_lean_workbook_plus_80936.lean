-- Prove2me | Theorems.Thm_lean_workbook_plus_80936
-- name    : lean_workbook_plus_80936
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/48e5352b-84fd-47ce-8f1d-3227235f70c6
-- statement:
--   For ${\max}(2x-1; x+1)$, it is $2x-1$ for $x \geq 2$ and $x+1$ for $x<2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80936 (x : ℝ) : max (2*x-1) (x+1) = if x ≥ 2 then 2*x-1 else x+1   :=  by sorry
