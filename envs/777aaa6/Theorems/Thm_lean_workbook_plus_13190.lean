-- Prove2me | Theorems.Thm_lean_workbook_plus_13190
-- name    : lean_workbook_plus_13190
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a0c6baa3-203d-405e-836d-16ce64abb37e
-- statement:
--   Prove that $\dfrac{(a+b+c)^2}{a+b+c+ab+bc+ca} \geq \dfrac{3(a+b+c)^2}{3(a+b+c)+(a+b+c)^2}=\dfrac{3(a+b+c)}{a+b+c+3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13190 : ∀ a b c : ℝ, (a + b + c) ^ 2 / (a + b + c + a * b + b * c + c * a) ≥ 3 * (a + b + c) ^ 2 / (3 * (a + b + c) + (a + b + c) ^ 2)   :=  by sorry
