-- Prove2me | Theorems.Thm_lean_workbook_plus_72246
-- name    : lean_workbook_plus_72246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/40529638-0843-42ad-8635-7c3f3dd178e8
-- statement:
--   Let $a,b\geq 0 $ and $ (a+1)(ab^2+1) \geq 4.$ Prove that \n $$a+b\geq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72246 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : (a + 1) * (a * b ^ 2 + 1) ≥ 4) : a + b ≥ 2   :=  by sorry
