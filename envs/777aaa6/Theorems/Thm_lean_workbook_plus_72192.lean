-- Prove2me | Theorems.Thm_lean_workbook_plus_72192
-- name    : lean_workbook_plus_72192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e84e97ad-2f1f-472d-89ce-75cbfcdd2594
-- statement:
--   Let $a,b,c>0$ and $a^2+b^2+c^2 \ge 4\sqrt{abc}$ , prove that: \n $ a+b+c \ge 2\sqrt{abc} $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72192 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 ≥ 4 * Real.sqrt (a * b * c)) : a + b + c ≥ 2 * Real.sqrt (a * b * c)   :=  by sorry
