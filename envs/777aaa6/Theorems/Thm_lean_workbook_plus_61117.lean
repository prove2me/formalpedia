-- Prove2me | Theorems.Thm_lean_workbook_plus_61117
-- name    : lean_workbook_plus_61117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f4906d82-7b20-4201-a6d2-827ed82a50aa
-- statement:
--   Prove that $\sqrt{(a-2)^2}=2-a$ for $a \leq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61117 (a : ℝ) (h : a ≤ 2) : Real.sqrt ((a - 2) ^ 2) = 2 - a   :=  by sorry
