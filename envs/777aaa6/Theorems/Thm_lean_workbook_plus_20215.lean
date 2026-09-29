-- Prove2me | Theorems.Thm_lean_workbook_plus_20215
-- name    : lean_workbook_plus_20215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/38236112-7af0-4288-bd6a-5384f51cf376
-- statement:
--   prove that $ a^{2}-ab+b^{2}\leq \frac{3(a^{2}+b^{2})}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20215 (a b : ℝ) : a ^ 2 - a * b + b ^ 2 ≤ (3 * (a ^ 2 + b ^ 2)) / 2   :=  by sorry
