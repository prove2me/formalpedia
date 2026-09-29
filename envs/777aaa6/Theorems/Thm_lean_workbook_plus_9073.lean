-- Prove2me | Theorems.Thm_lean_workbook_plus_9073
-- name    : lean_workbook_plus_9073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4791a32a-e958-4420-9387-07d471e1cc55
-- statement:
--   Let $a,b\geq0$ real. Prove that \n $$\frac{1}{(1+a)^2}+\frac{1}{(1+b)^2} \geq \frac{1}{1+ab}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9073 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) ≥ 1 / (1 + a * b)   :=  by sorry
