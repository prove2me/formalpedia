-- Prove2me | Theorems.Thm_lean_workbook_plus_45124
-- name    : lean_workbook_plus_45124
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ec3196b1-8bca-4fda-9867-b1ca4842e65a
-- statement:
--   Prove that for positive reals $a,b,c,d,$ and $a+b+c+d=1$ , $$\sum_{cyc}\frac{a^3}{b+c} \ge \frac{1}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45124 (hx: a + b + c + d = 1) (ha: a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0): a^3 / (b + c) + b^3 / (c + d) + c^3 / (d + a) + d^3 / (a + b) ≥ 1 / 8   :=  by sorry
