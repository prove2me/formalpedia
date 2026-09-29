-- Prove2me | Theorems.Thm_lean_workbook_plus_4758
-- name    : lean_workbook_plus_4758
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7a37f437-d0e9-415f-89c8-f9cab23f5e17
-- statement:
--   We have $\forall x\ge 1, e^{-x}\le 1\implies 1+e^{-x}\le 2\implies \frac{2}{x(1+e^{-x})}\ge \frac{1}{x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4758 : ∀ x : ℝ, 1 ≤ x → 2 / (x * (1 + exp (-x))) ≥ 1 / x   :=  by sorry
