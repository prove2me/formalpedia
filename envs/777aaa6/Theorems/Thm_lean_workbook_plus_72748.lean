-- Prove2me | Theorems.Thm_lean_workbook_plus_72748
-- name    : lean_workbook_plus_72748
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/265cd259-1520-45a7-9a6f-d963e9816fbd
-- statement:
--   Let 'x' be a positive real number such that: $x^{5} -x^{3} +x \ge 3$. Prove that $x^{6} \ge 5$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72748 (x : ℝ) (hx : 0 < x) (h : x^5 - x^3 + x ≥ 3) : x^6 ≥ 5   :=  by sorry
