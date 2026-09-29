-- Prove2me | Theorems.Thm_lean_workbook_plus_42060
-- name    : lean_workbook_plus_42060
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9b7df8ec-aff2-4c97-94ed-6f8a3b15c68c
-- statement:
--   Let $a, b, c>0$ . Prove the following inequality: $ (a+b)(b+c)(c+a)\geq 8abc $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42060 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c   :=  by sorry
