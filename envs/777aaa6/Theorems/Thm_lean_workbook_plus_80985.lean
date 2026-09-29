-- Prove2me | Theorems.Thm_lean_workbook_plus_80985
-- name    : lean_workbook_plus_80985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cf94c8a1-0be4-4c69-9002-08414009672e
-- statement:
--   4) $\lfloor x+2\rfloor=1$ (and so $x\in[-1,0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80985 (x : ℝ) (h : ⌊x + 2⌋ = 1) : x ∈ Set.Icc (-1) 0   :=  by sorry
