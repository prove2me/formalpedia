-- Prove2me | Theorems.Thm_lean_workbook_plus_68543
-- name    : lean_workbook_plus_68543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/7146d1f7-30f1-475f-99a8-e123a9b0d4ef
-- statement:
--   Given $a+b+c=a^2+b^2+c^2=a^3+b^3+c^3=0$, prove that $a=b=c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68543 (a b c : ℝ) (ha : a + b + c = 0) (hb : a ^ 2 + b ^ 2 + c ^ 2 = 0) (hc : a ^ 3 + b ^ 3 + c ^ 3 = 0) : a = 0 ∧ b = 0 ∧ c = 0   :=  by sorry
