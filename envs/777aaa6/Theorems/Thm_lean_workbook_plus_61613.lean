-- Prove2me | Theorems.Thm_lean_workbook_plus_61613
-- name    : lean_workbook_plus_61613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/71e707ef-7004-4137-aae1-1cd923c7f8e1
-- statement:
--   Setting $f(a)=a^2-a(b+c+d+e)+b^2+c^2+d^2+e^2.$ We prove that $f(a)\ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61613 (a b c d e : ℝ) : a^2 - a * (b + c + d + e) + b^2 + c^2 + d^2 + e^2 ≥ 0   :=  by sorry
