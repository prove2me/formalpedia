-- Prove2me | Theorems.Thm_lean_workbook_plus_41364
-- name    : lean_workbook_plus_41364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f3305cbb-c8f3-4e3b-8302-c8b790312aa6
-- statement:
--   Let $a,b$ be real numbers. Prove the inequality $ 2(a^4+a^2b^2+b^4)\ge 3(a^3b+ab^3).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41364 (a b : ℝ) : 2 * (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) ≥ 3 * (a ^ 3 * b + a * b ^ 3)   :=  by sorry
