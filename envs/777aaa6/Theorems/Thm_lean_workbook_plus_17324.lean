-- Prove2me | Theorems.Thm_lean_workbook_plus_17324
-- name    : lean_workbook_plus_17324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/483f27fe-0a1c-4192-91e4-2d323de4a54a
-- statement:
--   Given $a=-b$, $b=-c$, and $c=-a$, show that $a=b=c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17324 (a b c : ℝ) (hab : a = -b) (hbc : b = -c) (hca : c = -a) : a = 0 ∧ b = 0 ∧ c = 0   :=  by sorry
