-- Prove2me | Theorems.Thm_lean_workbook_plus_4771
-- name    : lean_workbook_plus_4771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4be55830-5a61-4a6a-b486-cd43007d2aa3
-- statement:
--   Let $a,b,c>0$ . Prove that: $\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \geq 3(\frac{1}{a+2b}+\frac{1}{b+2c}+\frac{1}{c+2a})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 3 * (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a))   :=  by sorry
