-- Prove2me | Theorems.Thm_lean_workbook_plus_28633
-- name    : lean_workbook_plus_28633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3a5723d4-f149-4a8c-aa80-e8ea14d6eb32
-- statement:
--   Prove that $ab(a^{2}+b^{2})+bc(b^{2}+c^{2})+ca(c^{2}+a^{2})\leq 2a^{4}+2b^{4}+2c^{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28633 : ∀ a b c : ℝ, a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ≤ 2 * a ^ 4 + 2 * b ^ 4 + 2 * c ^ 4   :=  by sorry
