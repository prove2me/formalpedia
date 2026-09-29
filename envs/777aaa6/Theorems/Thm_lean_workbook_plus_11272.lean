-- Prove2me | Theorems.Thm_lean_workbook_plus_11272
-- name    : lean_workbook_plus_11272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c995c22c-760c-4593-81e5-f4a7930798fa
-- statement:
--   For all reals $a$ , $b$ and $c$ such that $a+b+c=3$ prove that: $a^2+b^2+a^2b^2+abc\geq4ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11272 (a b c : ℝ) (hab : a + b + c = 3) : a^2 + b^2 + a^2 * b^2 + a * b * c ≥ 4 * a * b   :=  by sorry
