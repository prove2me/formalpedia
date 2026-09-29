-- Prove2me | Theorems.Thm_lean_workbook_plus_45269
-- name    : lean_workbook_plus_45269
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9adbce37-2aed-4d3d-a22c-598a27150cf0
-- statement:
--   Prove that $\frac{(a+b+c)^2}{ab+bc+ca} \ge \frac{9}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45269 : ∀ a b c : ℝ, (a + b + c) ^ 2 / (a * b + b * c + c * a) ≥ 9 / (a + b + c)   :=  by sorry
