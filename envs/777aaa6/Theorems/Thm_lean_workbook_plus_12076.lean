-- Prove2me | Theorems.Thm_lean_workbook_plus_12076
-- name    : lean_workbook_plus_12076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/08bef5de-3c2b-4b25-883c-95306498ef22
-- statement:
--   Prove that $ a^3+b^3+c^3\geq ab+bc+ac $ given $ a,b,c >0 $ and $ abc>1 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12076 (a b c : ℝ) (h : a>0 ∧ b>0 ∧ c>0 ∧ a * b * c > 1) :
  a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b + b * c + a * c   :=  by sorry
