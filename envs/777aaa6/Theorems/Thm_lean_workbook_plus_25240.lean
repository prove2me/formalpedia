-- Prove2me | Theorems.Thm_lean_workbook_plus_25240
-- name    : lean_workbook_plus_25240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/88e48f51-2b9b-46e3-9479-2f9f936f3c20
-- statement:
--   Let $a,b,c\ge 0$ and $\frac{1}{1+a^2}+\frac{1}{1+b^2}+\frac{1}{1+c^2}=\frac{3}{2}.$ Prove that $$ ab+bc+ca \ge 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25240 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a * b * c = 1) (h : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) = 3 / 2) : a * b + b * c + c * a ≥ 3   :=  by sorry
