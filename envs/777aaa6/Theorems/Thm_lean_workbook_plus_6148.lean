-- Prove2me | Theorems.Thm_lean_workbook_plus_6148
-- name    : lean_workbook_plus_6148
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/629c52f2-ac2e-45c9-b370-c9bd3c696ece
-- statement:
--   If $x^2+x-1\ne 0$ , we get $x=\frac{(x^3+2x^2)-(x^2+x)}{(x^2+x)-1}\in\mathbb Q$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6148 : ∀ x : ℚ, x^2 + x - 1 ≠ 0 → ∃ y : ℚ, x = (y^3 + 2*y^2 - (y^2 + y)) / (y^2 + y - 1)   :=  by sorry
