-- Prove2me | Theorems.Thm_lean_workbook_plus_16498
-- name    : lean_workbook_plus_16498
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f9ac5f34-d89d-4218-9a7d-406d70f56671
-- statement:
--   Let $a,b,c>0 $ and $ \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}=2.$ Prove that $$ \frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}=a+b+c$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16498 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) = 2 → a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) = a + b + c)   :=  by sorry
