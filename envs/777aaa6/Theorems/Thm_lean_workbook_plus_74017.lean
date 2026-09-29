-- Prove2me | Theorems.Thm_lean_workbook_plus_74017
-- name    : lean_workbook_plus_74017
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e153a7f1-e28f-45d9-885d-c1989ce53bea
-- statement:
--   2) $b>0$ : $x= \frac{a}{b}$ $\Leftrightarrow $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74017 (b : ℝ) (hb : 0 < b) : ∀ a : ℝ, (x = a / b ↔ b * x = a)   :=  by sorry
