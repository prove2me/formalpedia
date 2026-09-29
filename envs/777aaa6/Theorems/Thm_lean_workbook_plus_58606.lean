-- Prove2me | Theorems.Thm_lean_workbook_plus_58606
-- name    : lean_workbook_plus_58606
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0bd07933-162e-41e4-baa4-c0b75d2dc19b
-- statement:
--   Prove that for positive reals $a,b,c,d,$ and $a+b+c+d=1$ , $$\sum_{cyc}\frac{a^3}{b+c} \ge \frac{1}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58606 (hx: a + b + c + d = 1) : a^3 / (b + c) + b^3 / (c + d) + c^3 / (d + a) + d^3 / (a + b) ≥ 1 / 8   :=  by sorry
