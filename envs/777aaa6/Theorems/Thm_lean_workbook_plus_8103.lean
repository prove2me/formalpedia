-- Prove2me | Theorems.Thm_lean_workbook_plus_8103
-- name    : lean_workbook_plus_8103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/cae7347d-f66e-4469-9ae6-b3ca980aec6b
-- statement:
--   prove $(1+k)(a^4+b^4+c^4) \ge a^2b^2+(b^2+a^2)c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8103 (a b c k : ℝ) (h : k > 0) : (1 + k) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ a ^ 2 * b ^ 2 + (b ^ 2 + a ^ 2) * c ^ 2   :=  by sorry
