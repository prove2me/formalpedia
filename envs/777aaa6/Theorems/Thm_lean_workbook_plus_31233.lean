-- Prove2me | Theorems.Thm_lean_workbook_plus_31233
-- name    : lean_workbook_plus_31233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c587aa26-2e71-4f53-a349-bc0185e8f8b6
-- statement:
--   Let a; b; c be positive integers. Prove that \n $$ \frac{(b+c-a)^2}{(b+c)^2+a^2} + \frac{(c+a-b)^2}{(c+a)^2+b^2} + \frac{(a+b-c)^2}{(a+b)^2+c^2} \geq \frac{3}{5}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31233 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3/5   :=  by sorry
