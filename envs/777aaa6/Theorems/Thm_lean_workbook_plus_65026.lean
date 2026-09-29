-- Prove2me | Theorems.Thm_lean_workbook_plus_65026
-- name    : lean_workbook_plus_65026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/57a25305-4dda-46cc-ab7f-b09fd51848f7
-- statement:
--   Further, $2(a^{2} + b^{2} + c^{2}) + ab + ac + bc\geq 3(ab + ac + bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65026 : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b + a * c + b * c ≥ 3 * (a * b + a * c + b * c)   :=  by sorry
