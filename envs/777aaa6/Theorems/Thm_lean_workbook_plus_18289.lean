-- Prove2me | Theorems.Thm_lean_workbook_plus_18289
-- name    : lean_workbook_plus_18289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bd749373-6b28-45bf-9d2a-6bbe7fcf5474
-- statement:
--   Is this true: $a^2b^2+a^2+b^2+2(a+b)+1 \ge \ 2(a^2b+ab^2)$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18289 (a b : ℝ) : a^2 * b^2 + a^2 + b^2 + 2 * (a + b) + 1 ≥ 2 * (a^2 * b + a * b^2)   :=  by sorry
