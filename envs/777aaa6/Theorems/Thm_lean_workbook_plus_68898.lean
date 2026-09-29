-- Prove2me | Theorems.Thm_lean_workbook_plus_68898
-- name    : lean_workbook_plus_68898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e72427cd-7ef2-400a-ad70-9d2364a326d2
-- statement:
--   $f(-1)=f(-1)^2$ and so $f(-1)\in\{0,1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68898 (f : ℤ → ℤ) (h : f (-1) = f (-1) ^ 2) : f (-1) = 0 ∨ f (-1) = 1   :=  by sorry
