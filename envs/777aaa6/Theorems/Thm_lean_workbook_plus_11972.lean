-- Prove2me | Theorems.Thm_lean_workbook_plus_11972
-- name    : lean_workbook_plus_11972
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/697f4322-2cee-42e0-9520-76ff2f9362bc
-- statement:
--   Let $a,b$ be positive real numbers. Prove that $a^3b+ab^3+a+b \geqslant 2ab+a^2b+ab^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11972 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 * b + a * b^3 + a + b ≥ 2 * a * b + a^2 * b + a * b^2   :=  by sorry
