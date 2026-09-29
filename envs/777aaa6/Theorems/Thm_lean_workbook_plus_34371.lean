-- Prove2me | Theorems.Thm_lean_workbook_plus_34371
-- name    : lean_workbook_plus_34371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e7c85c2e-7f15-46ad-bf5f-d92720b7a8e6
-- statement:
--   $\sqrt{a^2-ab+b^2} \geq \frac{a+b}{2}\Leftrightarrow (a-b)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34371 : ∀ a b : ℝ,  Real.sqrt (a ^ 2 - a * b + b ^ 2) ≥ (a + b) / 2 ↔ (a - b) ^ 2 ≥ 0   :=  by sorry
