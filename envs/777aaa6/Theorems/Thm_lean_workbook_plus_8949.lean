-- Prove2me | Theorems.Thm_lean_workbook_plus_8949
-- name    : lean_workbook_plus_8949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8e4a8278-6ebb-413e-860c-47e575f90a4c
-- statement:
--   Let $a, b \geq 1$. Prove that $\frac{1}{1+a^2}+\frac{1}{1+b^2}\geq \frac{2}{1+ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8949 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (1 / (1 + a^2) + 1 / (1 + b^2)) ≥ 2 / (1 + a * b)   :=  by sorry
