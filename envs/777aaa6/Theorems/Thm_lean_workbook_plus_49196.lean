-- Prove2me | Theorems.Thm_lean_workbook_plus_49196
-- name    : lean_workbook_plus_49196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ea90cb36-bd7a-4582-8f7e-b9cda2e95b2b
-- statement:
--   Let $a,b,c$ be reals such that $ a\geq 2$ and $ abc=1.$ Prove that \n $$\frac{1}{2}a^2+b^2+c^2-bc \geq \frac{5}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49196 (a b c: ℝ) (h1: a >= 2) (h2: a * b * c = 1) : (1 / 2) * a ^ 2 + b ^ 2 + c ^ 2 - b * c >= 5 / 2   :=  by sorry
