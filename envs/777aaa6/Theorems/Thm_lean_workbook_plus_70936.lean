-- Prove2me | Theorems.Thm_lean_workbook_plus_70936
-- name    : lean_workbook_plus_70936
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c6c20120-c6fc-4609-abbb-696ba89c88be
-- statement:
--   Let $a,b,c \geq 1$ such that $abc=3$ . Prove that \n\n $$(a+1)(b+1)(c+1) \geq 8(a-1)(b-1)(c-1).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70936 (a b c : ℝ) (habc : a * b * c = 3) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : (a + 1) * (b + 1) * (c + 1) ≥ 8 * (a - 1) * (b - 1) * (c - 1)   :=  by sorry
