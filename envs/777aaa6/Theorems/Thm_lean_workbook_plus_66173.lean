-- Prove2me | Theorems.Thm_lean_workbook_plus_66173
-- name    : lean_workbook_plus_66173
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c75e114f-0b5e-4638-9537-d81e26b54df3
-- statement:
--   Prove that $|a|+|b|+|c|+|a+b+c| \geq |b+c|+|c+a|+|a+b|$ for reals $a,b,c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66173 (a b c : ℝ) : |a| + |b| + |c| + |a + b + c| ≥ |b + c| + |c + a| + |a + b|   :=  by sorry
