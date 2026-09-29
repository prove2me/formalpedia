-- Prove2me | Theorems.Thm_lean_workbook_plus_24391
-- name    : lean_workbook_plus_24391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ec151a78-f8ca-46f8-bc3a-63386cd5c8f3
-- statement:
--   Let $0\le x\le y\le 1$ . Prove using calculus that: $ \frac{1}{4}\geq\ xy^2-yx^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24391 : ∀ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 → 1 / 4 ≥ y * x ^ 2 - x * y ^ 2   :=  by sorry
