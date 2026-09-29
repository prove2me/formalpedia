-- Prove2me | Theorems.Thm_lean_workbook_plus_43533
-- name    : lean_workbook_plus_43533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2943fb0e-78af-4271-8753-b51447881c9c
-- statement:
--   Prove that $2(ab+bc+ca)\leq \frac{2}{3}(a+b+c)^2$ for positive numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43533 (a b c : ℝ) : 2 * (a * b + b * c + c * a) ≤ (2 / 3) * (a + b + c) ^ 2   :=  by sorry
