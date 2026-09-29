-- Prove2me | Theorems.Thm_lean_workbook_plus_71517
-- name    : lean_workbook_plus_71517
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d551adc1-9bcd-4a57-bc9c-59e818160fef
-- statement:
--   Let $a,b,c>0$ and $a^2+b^2+c^2=a^3+b^3+c^3. $ Prove that\n\n $$ abc\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71517 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = a^3 + b^3 + c^3) : a * b * c ≤ 1   :=  by sorry
