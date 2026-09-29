-- Prove2me | Theorems.Thm_lean_workbook_plus_16639
-- name    : lean_workbook_plus_16639
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9d8b6e3d-e47a-4901-8a0d-91c39132fa40
-- statement:
--   Prove that $5(\cos^2(a) + \sin^2(a))\left(\frac{1}{\cos^2(a)} + \frac{4}{\sin^2(a)}\right) \geq 5(1 + 2)^2 = 45$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16639 : ∀ a : ℝ, 5 * (cos a ^ 2 + sin a ^ 2) * (1 / cos a ^ 2 + 4 / sin a ^ 2) ≥ 45   :=  by sorry
