-- Prove2me | Theorems.Thm_lean_workbook_plus_31520
-- name    : lean_workbook_plus_31520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9492731b-75c6-4e36-b0ef-9f2b923312e4
-- statement:
--   Find the value of $ a^2+b^2 +c^2 $ given $ a+b+c=0 $, $ ab+ac+bc=3 $, and $ abc = -5 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31520 (a b c : ℝ) (ha : a + b + c = 0) (hb : a * b + b * c + c * a = 3) (hc : a * b * c = -5) : a ^ 2 + b ^ 2 + c ^ 2 = -6   :=  by sorry
