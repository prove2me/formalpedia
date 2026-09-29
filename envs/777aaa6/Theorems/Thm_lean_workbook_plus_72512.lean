-- Prove2me | Theorems.Thm_lean_workbook_plus_72512
-- name    : lean_workbook_plus_72512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/74c5ce54-ba2f-41bd-980e-ebc0b3859a8b
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=12,ab+bc+ca=45. $ Then $50\leq abc\leq 54.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72512 (a b c : ℝ) (h1 : a + b + c = 12) (h2 : a * b + b * c + c * a = 45) : 50 ≤ a * b * c ∧ a * b * c ≤ 54   :=  by sorry
