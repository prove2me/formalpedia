-- Prove2me | Theorems.Thm_lean_workbook_plus_57336
-- name    : lean_workbook_plus_57336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2a859ca1-8f07-4329-aa3c-f5a766ae0e52
-- statement:
--   Prove that $14(a^{2}+b^{2})+53ab\leq\frac{81}{4}(a+b)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57336 (a b : ℝ) :
  14 * (a ^ 2 + b ^ 2) + 53 * a * b ≤ (81 / 4) * (a + b) ^ 2   :=  by sorry
