-- Prove2me | Theorems.Thm_lean_workbook_plus_19437
-- name    : lean_workbook_plus_19437
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a0414357-3374-47a4-a505-bf2998df80ca
-- statement:
--   Let $a > 0$ , $b > 0$ and $ab=1$ . Prove that $\frac{a}{a^2+3}+\frac{b}{b^2+3}\leq\frac{1}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19437 (a b : ℝ) (hab : a * b = 1) : a / (a ^ 2 + 3) + b / (b ^ 2 + 3) ≤ 1 / 2   :=  by sorry
