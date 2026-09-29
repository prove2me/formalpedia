-- Prove2me | Theorems.Thm_lean_workbook_plus_5724
-- name    : lean_workbook_plus_5724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e5ad6fed-77f2-4720-83aa-9adc4c1d4ea1
-- statement:
--   Let $ a,b,c>0$ . Show that \n $ \frac{a+b+c}{abc}\leq{\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5724 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (a * b * c) ≤ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2   :=  by sorry
