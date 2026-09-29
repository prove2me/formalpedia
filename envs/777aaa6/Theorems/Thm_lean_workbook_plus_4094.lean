-- Prove2me | Theorems.Thm_lean_workbook_plus_4094
-- name    : lean_workbook_plus_4094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b53a15ae-3cc3-4805-8761-54ec4f1b7bff
-- statement:
--   Let $ a,\ b,\ c$ be real numbers. Prove that $ |x|\leq\frac{1}{2}x^{2}+\frac{1}{2}\Longleftrightarrow (|x|-1)^{2}\geq 0$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4094 (x : ℝ) : |x| ≤ 1/2 * x^2 + 1/2 ↔ (|x| - 1)^2 ≥ 0   :=  by sorry
