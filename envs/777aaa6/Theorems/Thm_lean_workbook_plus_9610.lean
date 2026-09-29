-- Prove2me | Theorems.Thm_lean_workbook_plus_9610
-- name    : lean_workbook_plus_9610
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/36852b8e-2c85-485b-8e0e-722c6935690a
-- statement:
--   Let $a,b $ be real numbers such that $ a(a+1)^2+b(b+1)^2=8$ . Prove that\n $$ a+b\leq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9610 (a b : ℝ) (h : a * (a + 1) ^ 2 + b * (b + 1) ^ 2 = 8) : a + b ≤ 2   :=  by sorry
