-- Prove2me | Theorems.Thm_lean_workbook_plus_59787
-- name    : lean_workbook_plus_59787
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f7fb18e1-a335-4cf0-8bca-ba05b5cf0be0
-- statement:
--   Let $a, b, c \geq0$ . Prove that \n $$ \frac{1}{8} \cdot \frac{(2+a) (2+b) (2+c)} {(1+a) (1+b) (1+c)} \geq \frac{4-a-b-c} {4+a+b+c} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59787 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c))) ≥ (4 - a - b - c) / (4 + a + b + c)   :=  by sorry
