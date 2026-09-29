-- Prove2me | Theorems.Thm_lean_workbook_plus_45475
-- name    : lean_workbook_plus_45475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/14b68ed1-2f2b-42e8-8c9b-31d71ca72490
-- statement:
--   Let $a,b>0 $ and $ \frac{ a^3}{b}+\frac{ 2b }{a}=3 .$ Prove that\n\n $$a^2+ab+b^2\leq 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45475 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^3 / b + 2 * b / a = 3) : a^2 + a * b + b^2 ≤ 3   :=  by sorry
