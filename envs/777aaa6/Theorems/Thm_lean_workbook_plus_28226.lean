-- Prove2me | Theorems.Thm_lean_workbook_plus_28226
-- name    : lean_workbook_plus_28226
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fb7ded28-5d6a-4828-9d88-7fdc5a20d473
-- statement:
--   We also have: \n $$3\,\sqrt {4\,{a}^{2}+4\,{b}^{2}+4\,{c}^{2}+6\,abc}\leq \sqrt {15\,{a}^{3}+1}+\sqrt {15\,{b}^{3}+1}+\sqrt {15\,{c}^{3}+1}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28226 :  ∀ a b c : ℝ, 3 * Real.sqrt (4 * a ^ 2 + 4 * b ^ 2 + 4 * c ^ 2 + 6 * a * b * c) ≤ Real.sqrt (15 * a ^ 3 + 1) + Real.sqrt (15 * b ^ 3 + 1) + Real.sqrt (15 * c ^ 3 + 1)   :=  by sorry
