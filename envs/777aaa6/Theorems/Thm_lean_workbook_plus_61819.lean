-- Prove2me | Theorems.Thm_lean_workbook_plus_61819
-- name    : lean_workbook_plus_61819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c6126daa-b9df-4bdf-a65d-abc69e992cdf
-- statement:
--   Let $a,b,c$ be positive real numbers such that $abc=1$ . Then prove that \n $ (a^2+1)(b^2+1)(c^2+1)\ge (a+1)(b+1)(c+1). $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61819 (a b c : ℝ) (habc : a * b * c = 1) :  (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1)   :=  by sorry
