-- Prove2me | Theorems.Thm_lean_workbook_plus_80763
-- name    : lean_workbook_plus_80763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/39f80df9-61d6-4d9c-a040-306d3751ee26
-- statement:
--   If $0<x<1$ , prove that $2x(1-x)^{2}\leq\frac{8}{27}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80763 : ∀ x : ℝ, 0 < x ∧ x < 1 → 2 * x * (1 - x) ^ 2 ≤ 8 / 27   :=  by sorry
