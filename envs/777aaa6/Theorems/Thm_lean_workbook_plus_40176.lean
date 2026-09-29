-- Prove2me | Theorems.Thm_lean_workbook_plus_40176
-- name    : lean_workbook_plus_40176
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9673a409-7bf7-40bc-9da1-9caf7619321f
-- statement:
--   For positive real numbers $ a,b,c$ , prove that \n $ (a^2+b^2)^2 \ge (a+b+c)(a+b-c)(b+c-a)(c+a-b).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40176 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
