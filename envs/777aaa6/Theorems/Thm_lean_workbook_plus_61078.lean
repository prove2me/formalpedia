-- Prove2me | Theorems.Thm_lean_workbook_plus_61078
-- name    : lean_workbook_plus_61078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ebcc4a59-611c-458b-8b77-50e432c36d97
-- statement:
--   Let $a, b \geq 0$ . Prove that \n $$ \frac{1}{4} \cdot \frac{(2+a) (2+b)} {(1+a) (1+b)} \geq \frac{4-a-b} {4+a+b} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61078 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / 4) * ((2 + a) * (2 + b) / ((1 + a) * (1 + b))) ≥ (4 - a - b) / (4 + a + b)   :=  by sorry
