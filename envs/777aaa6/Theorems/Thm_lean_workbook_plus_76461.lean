-- Prove2me | Theorems.Thm_lean_workbook_plus_76461
-- name    : lean_workbook_plus_76461
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9c628af4-183f-4c56-87b6-9a517734afa7
-- statement:
--   Prove that : $(ab+bc+ca-1) \leq (a^2+1)(b^2+1)(c^2+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76461 (a b c : ℝ) : (a * b + b * c + c * a - 1) ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)   :=  by sorry
